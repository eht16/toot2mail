#!/usr/bin/env python3
#
# This software may be modified and distributed under the terms
# of the MIT license.  See the LICENSE file for details.

from configparser import ConfigParser
from datetime import datetime
from email.header import Header
from email.mime.image import MIMEImage
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from email.utils import COMMASPACE, formatdate
from pathlib import Path
from random import randint
from time import sleep
from urllib.parse import urljoin, urlsplit
import io
import json
import logging
import logging.handlers
import os
import smtplib
import socket
import sys

import requests
import requests_html
try:
    from PIL import Image
except ImportError:
    Image = None  # skip image processing if pillow is missing


CONFIG_FILENAME = '~/.config/toot2mail.conf'
MAIL_MESSAGE_TEMPLATE = '''{toot}

{card}
--------------------------------
Videos: {videos}
Posted by: {posted_by}
Boosted by: {boosted_by}
In Reply To: {in_reply_to_url}
URL: {url}
Timeline: https://{hostname}/@{username}/with_replies
'''

CARD_TEMPLATE = '''
--------------------------------
Card URL:   {card_url}:
Card Title: {card_title}'''


# Taken from Mastodon.py's AttribAccessDict
# (https://github.com/halcy/Mastodon.py/blob/master/mastodon/Mastodon.py#L128)
class AttribAccessDict(dict):
    def __getattr__(self, attr):
        if attr in self:
            return self[attr]
        raise AttributeError("Attribute not found: " + str(attr))

    def __setattr__(self, attr, val):
        if attr in self:
            raise AttributeError("Attribute-style access is read only")
        super().__setattr__(attr, val)


class Toot(AttribAccessDict):

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

        self.in_reply_to = None
        self.is_reply = bool(self.in_reply_to_id)
        self.is_boost = bool(self.reblog)

    @property
    def content(self):
        return self.reblog.content if self.is_boost else self.get('content')

    @property
    def card(self):
        card = self.reblog.card if self.is_boost else self.get('card')
        return AttribAccessDict(card or {})

    @property
    def reblog(self):
        return Toot(self.get('reblog') or {})

    @property
    def account(self):
        return AttribAccessDict(self.get('account'))

    def get_hostname(self):
        parsed_url = urlsplit(self.url)
        return parsed_url.netloc

    def get_uid(self):
        acct = self.account.acct
        if '@' in acct:
            return acct.lower()

        username_lowercase = self.account.username.lower()
        return f'{username_lowercase}@{self.get_hostname()}'

    def get_username(self, compound=True):
        if self.is_boost:
            if compound:
                return f'{self.account.username}: {self.reblog.account.username}'

            return self.reblog.account.username

        return self.account.username

    @property
    def media_attachments(self):
        if self.is_boost and self.reblog.media_attachments:
            media_attachments = self.reblog.media_attachments
        else:
            media_attachments = self.get('media_attachments') or []

        return [AttribAccessDict(media_attachment) for media_attachment in media_attachments]


class MastodonEmailProcessor:

    def __init__(self):
        self._config = None
        self._proxies = {}
        self._timeout = {}
        self._timeline_limit = None
        self._state_file_path = None
        self._lock_file_path = None
        self._image_maximum_size = None
        self._mail_maximum_subject_length = None
        self._mail_from = None
        self._mail_recipient = None
        self._mail_server_hostname = None
        self._mail_server_port = None
        self._logger = None
        self._usernames = None
        self._references = None
        self._toot_state = None

    def process(self):
        self._setup_config()
        self._setup_logger()
        self._log_hello()
        self._assert_not_already_running()
        self._write_lock()

        self._read_toot_state()
        try:
            for username, hostname, exclude_replies, exclude_boosts in self._usernames:
                self._process_user(username, hostname, exclude_replies, exclude_boosts)
                sleep(randint(3, 10))  # give the remote instance a little time
        finally:
            self._write_toot_state()
            self._remove_lock()

        self._log_farewell()

    def _setup_config(self):
        config_parser = ConfigParser(allow_no_value=True)
        # read config file from location as specified via command line but fail it if doesn't exist
        config_filename = Path(CONFIG_FILENAME).expanduser()
        config_file_paths = ('toot2mail.conf', config_filename)
        config_parser.read(config_file_paths)

        self._timeout = config_parser.getfloat('settings', 'timeout', fallback=60)
        self._timeline_limit = config_parser.get('settings', 'timeline_limit')
        self._state_file_path = Path(config_parser.get('settings', 'state_file_path'))
        self._lock_file_path = Path(config_parser.get('settings', 'lock_file_path'))
        self._mail_maximum_subject_length = config_parser.getint('settings', 'mail_maximum_subject_length')
        self._mail_from = config_parser.get('settings', 'mail_from')
        self._mail_recipient = config_parser.get('settings', 'mail_recipient')
        self._mail_server_hostname = config_parser.get('settings', 'mail_server_hostname')
        self._mail_server_port = config_parser.getint('settings', 'mail_server_port')

        image_maximum_size = config_parser.get('settings', 'image_maximum_size', fallback=None)
        if image_maximum_size:
            self._image_maximum_size = [int(value) for value in image_maximum_size.split(',')]

        proxy = config_parser.get('settings', 'proxy')
        if proxy:
            os.environ['http_proxy'] = proxy
            os.environ['https_proxy'] = proxy
            self._proxies = {'http': proxy, 'https': proxy}

        self._usernames = []
        for uid, flags in config_parser.items('accounts'):
            username, hostname = uid.split('@')
            flags = flags.split(',')
            exclude_replies = 'noreplies' in flags
            exclude_boosts = 'noboosts' in flags
            self._usernames.append((username, hostname, exclude_replies, exclude_boosts))

    def _setup_logger(self):
        me = Path(__file__).name
        stream_handler = logging.StreamHandler()
        stream_handler.setLevel(logging.WARNING)
        syslog_handler = logging.handlers.SysLogHandler(address='/dev/log')
        syslog_handler.ident = f'{me}: '
        logging.basicConfig(
            format='[%(levelname)+8s] [%(process)-8s] [%(name)-30s] %(message)s',
            level=logging.INFO,
            handlers=[syslog_handler, stream_handler])

        self._logger = logging.getLogger(me)

    def _assert_not_already_running(self):
        if self._lock_file_path.exists():
            self._logger.info('Already running. Aborting.')
            raise RuntimeError('Already running')

    def _write_lock(self):
        self._lock_file_path.touch()

    def _log_hello(self):
        self._logger.info('Starting...')

    def _log_farewell(self):
        self._logger.info('Finished.')

    def _read_toot_state(self):
        if not self._state_file_path.exists():
            self._toot_state = {}
        else:
            with open(self._state_file_path, encoding='utf-8') as state_file:
                self._toot_state = json.load(state_file)

    def _process_user(self, username, hostname, exclude_replies, exclude_boosts):
        try:
            self._logger.info('Processing new toots for "%s@%s"', username, hostname)

            toots_count = 0
            skipped_toots_count = 0
            toots = self._get_toots(username, hostname)
            for toot in toots:
                if self._is_toot_already_processed(toot):
                    skipped_toots_count += 1
                    continue

                if exclude_replies and toot.is_reply:
                    continue
                if exclude_boosts and toot.is_boost:
                    continue

                self._process_toot(toot, username, hostname)
                toots_count += 1

            self._logger.info(
                'Processed %s new toot(s) and skipped %s already processed toot(s) for "%s@%s"',
                toots_count, skipped_toots_count, username, hostname)
        except Exception as exc:
            self._logger.exception('An error occurred while processing "%s@%s": %s',
                                   username, hostname, exc)

    def _get_toots(self, username, hostname):
        account_id = self._get_account_id(username, hostname)
        url = f'api/v1/accounts/{account_id}/statuses'
        toot_dicts = self._request(url, hostname, query_params={'limit': self._timeline_limit})
        toots = [Toot(toot_dict) for toot_dict in toot_dicts]
        return toots

    def _get_account_id(self, username, hostname):
        uid = f'{username}@{hostname}'
        user = self._toot_state.get(uid)
        if user:
            account_id = user['account_id']
        else:
            account = self._request('api/v1/accounts/lookup', hostname,
                                    query_params={'acct': username})
            account_id = account['id']
            self._toot_state[uid] = {'account_id': account_id, 'toots': []}

        return account_id

    def _request(self, api_endpoint, hostname, query_params=None):
        if not hostname:
            raise ValueError('No Mastodon host set!')

        url = urljoin(f'https://{hostname}', api_endpoint)
        response = requests.get(url, params=query_params, proxies=self._proxies,
                                timeout=self._timeout)
        response.raise_for_status()

        response_json = response.json()
        return response_json

    def _is_toot_already_processed(self, toot):
        uid = toot.get_uid()
        user = self._toot_state.get(uid, {})
        user_toots = user.get('toots', [])
        return bool(toot.uri in user_toots)

    def _process_toot(self, toot, username, hostname):
        self._references = set()
        try:
            self._get_toot_in_reply_to(toot, hostname)
            mail_from = self._factor_mail_from(toot)
            subject = self._factor_mail_subject(toot)
            message = self._factor_mail_message(toot, username)
            toot_timestamp = self._factor_toot_timestamp(toot)
            attachments = self._factor_toot_attachments(toot)
            headers = self._factor_mail_headers(toot)
            # send the mail
            self._send_mail(mail_from, subject, message, toot_timestamp, attachments, headers)
            # remember toot
            self._add_toot_to_toot_state(toot)
        except Exception as exc:
            self._logger.exception('An error occurred while processing "%s@%s" at toot %s: %s',
                                   username, toot.get_hostname(), toot.id, exc)

    def _get_toot_in_reply_to(self, toot, hostname):
        if toot.in_reply_to_id:
            in_reply_to = self._request(f'api/v1/statuses/{toot.in_reply_to_id}', hostname)
            if in_reply_to:
                toot.in_reply_to = Toot(in_reply_to)
                if not self._is_toot_already_processed(toot.in_reply_to):
                    self._process_toot(toot.in_reply_to, toot.in_reply_to.account.username,
                                       hostname)

    def _factor_mail_message(self, toot, username):
        message = MAIL_MESSAGE_TEMPLATE.format(
            toot=self._html2text(toot.content),
            username=username,
            posted_by=toot.get_username(compound=False),
            boosted_by=toot.account.username if toot.is_boost else '-',
            in_reply_to_url=toot.in_reply_to.url if toot.is_reply else '-',
            videos=self._factor_video_list(toot),
            card=self._factor_card(toot),
            url=toot.reblog.url if toot.is_boost else toot.url,
            hostname=toot.get_hostname())
        return message

    def _factor_video_list(self, toot):
        videos = ''
        for media in toot.media_attachments:
            if media.type not in ('gifv', 'video'):
                continue

            video_url = media.url
            videos += f'\n  - {video_url}'

        return videos or '-'

    def _factor_card(self, toot):
        card = toot.card
        if card:
            return CARD_TEMPLATE.format(card_url=card.url, card_title=card.title)

        return ''

    def _factor_mail_from(self, toot):
        encoded_name = Header(toot.get_username(), 'utf-8').encode()
        return f'{encoded_name} <{self._mail_from}>'

    def _factor_mail_subject(self, toot):
        content = toot.content
        subject = self._html2text(content)

        if len(subject) > self._mail_maximum_subject_length:
            subject = subject[:self._mail_maximum_subject_length] + '...'

        return Header(subject or '...', 'utf-8')

    def _html2text(self, html):
        if not html:
            return html

        return requests_html.HTML(html=html).text

    def _factor_toot_timestamp(self, toot):
        toot_created_at = toot.created_at
        if toot_created_at.endswith('Z') and sys.version_info < (3, 11):
            toot_created_at = toot_created_at[:-1]  # strip TZ info, Python < 3.11 cannot handle it

        created_at = datetime.fromisoformat(toot_created_at)
        return created_at.timestamp()

    def _factor_toot_attachments(self, toot):
        attachments = []
        for media in toot.media_attachments:
            if media.type not in ('gifv', 'image', 'video'):
                continue

            media_url = media.url if media.type == 'image' else media.preview_url

            file_name = Path(media_url).name
            file_content = self._get_image(media_url)
            attachments.append((file_name, file_content))

        return attachments

    def _get_image(self, image_url):
        self._logger.info('Retrieve image "%s"', image_url)
        try:
            response = requests.get(image_url, proxies=self._proxies, timeout=self._timeout)
            response.raise_for_status()
        except requests.exceptions.HTTPError as err:
            self._logger.warning('Unable to download image "%s": %s', image_url, err)
            return None
        else:
            image_data = self._downscale_image(response.content)
            return image_data

    def _downscale_image(self, image_data):
        if Image is None:  # pillow / PIL not installed
            return image_data

        if not self._image_maximum_size:
            return image_data

        max_width = self._image_maximum_size[0]
        max_height = self._image_maximum_size[1]
        try:
            image_data_bytes = io.BytesIO(image_data)
            image = Image.open(image_data_bytes)
            if image.size[0] > max_width or image.size[1] > max_height:
                image.thumbnail((max_width, max_height))
                result = io.BytesIO()
                image.save(result, image.format)
                return result.getvalue()
        except Exception as err:
            self._logger.warning('Unable to downscale image: %s', err)

        return image_data

    def _factor_mail_headers(self, toot):
        fqdn = socket.getfqdn()
        hostname = toot.get_hostname()
        headers = {'X-Toot-URI': f'{toot.uri}',
                   'X-Toot-Account': f'{toot.get_uid()}',
                   'Message-ID': f'<{toot.account.id}.{hostname}.{toot.id}@{fqdn}>'}
        if toot.is_reply and toot.in_reply_to:
            in_reply_to_hostname = toot.in_reply_to.get_hostname()
            headers['In-Reply-To'] = f'<{toot.in_reply_to_account_id}.{in_reply_to_hostname}.' \
                                     f'{toot.in_reply_to.id}@{fqdn}>'

        return headers

    def _send_mail(self, mail_from, subject, message, date, files=None, headers=None):
        if files:
            msg = MIMEMultipart()
            msg.attach(MIMEText(message))
            for file_name, file_content in files:
                if not file_content:
                    continue
                try:
                    part = MIMEImage(file_content)
                except TypeError:
                    part = MIMEImage(file_content, 'png')
                part.add_header('Content-Disposition', f'attachment; filename="{file_name}"')
                msg.attach(part)
        else:
            msg = MIMEText(message, _charset='utf-8')

        recipients = [self._mail_recipient]
        msg['From'] = mail_from
        msg['To'] = COMMASPACE.join(recipients)
        msg['Date'] = formatdate(date)
        msg['Subject'] = subject
        if headers is not None:
            for key, value in headers.items():
                msg.add_header(key, value)

        smtp = smtplib.SMTP(self._mail_server_hostname, self._mail_server_port)
        smtp.sendmail(self._mail_recipient, recipients, msg.as_string())
        smtp.quit()

    def _add_toot_to_toot_state(self, toot):
        uid = toot.get_uid()
        user = self._toot_state.setdefault(uid, {'account_id': toot.account.id, 'toots': []})
        user['toots'].append(toot.uri)

    def _write_toot_state(self):
        with open(self._state_file_path, 'w', encoding='utf-8') as state_file:
            json.dump(self._toot_state, state_file, indent=2)

    def _remove_lock(self):
        self._lock_file_path.unlink()


def main():
    processor = MastodonEmailProcessor()
    processor.process()


if __name__ == '__main__':
    main()
