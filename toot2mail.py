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
from urllib.parse import urljoin
import json
import logging
import logging.handlers
import os
import smtplib
import sys

import requests
import requests_html


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

        self.is_reply = bool(self.in_reply_to_id)
        self.is_boost = bool(self.reblog)

    @property
    def content(self):
        return self.reblog.content if self.is_boost else self.get('content')

    @property
    def uri(self):
        return self.reblog.uri if self.is_boost else self.get('uri')

    @property
    def url(self):
        return self.reblog.url if self.is_boost else self.get('url')

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
        self._timeline_limit = None
        self._state_file_path = None
        self._lock_file_path = None
        self._mail_maximum_subject_length = None
        self._mail_from = None
        self._mail_recipient = None
        self._mail_server_hostname = None
        self._mail_server_port = None
        self._logger = None
        self._usernames = None
        self._username = None
        self._hostname = None
        self._username_exclude_replies = None
        self._username_exclude_boosts = None
        self._toot_state = None
        self._account_id_by_username = None

    def process(self):
        self._setup_config()
        self._setup_logger()
        self._log_hello()
        self._assert_not_already_running()
        self._write_lock()

        self._read_toot_state()
        try:
            for self._username, self._hostname, self._username_exclude_replies, \
                    self._username_exclude_boosts in self._usernames:
                self._process_user()
                sleep(randint(5, 30))  # give the remote instance a little time
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

        self._timeline_limit = config_parser.get('settings', 'timeline_limit')
        self._state_file_path = Path(config_parser.get('settings', 'state_file_path'))
        self._lock_file_path = Path(config_parser.get('settings', 'lock_file_path'))
        self._mail_maximum_subject_length = config_parser.getint('settings', 'mail_maximum_subject_length')
        self._mail_from = config_parser.get('settings', 'mail_from')
        self._mail_recipient = config_parser.get('settings', 'mail_recipient')
        self._mail_server_hostname = config_parser.get('settings', 'mail_server_hostname')
        self._mail_server_port = config_parser.getint('settings', 'mail_server_port')

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
        syslog_handler = logging.handlers.SysLogHandler(address='/dev/log')
        syslog_handler.ident = f'{me}: '
        logging.basicConfig(
            format='[%(levelname)+8s] [%(process)-8s] [%(name)-30s] %(message)s',
            level=logging.INFO,
            handlers=[syslog_handler])

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
            self._account_id_by_username = {}
        else:
            with open(self._state_file_path, encoding='utf-8') as state_file:
                self._toot_state = json.load(state_file)
            self._account_id_by_username = {user['username']: account_id
                                            for account_id, user
                                            in self._toot_state.items()}

    def _process_user(self):
        self._logger.info('Processing new toots for "%s@%s"', self._username, self._hostname)

        toots = self._get_toots()

        # handle output
        toots_count = 0
        skipped_toots_count = 0
        for toot in toots:
            if self._is_toot_already_processed(toot):
                skipped_toots_count += 1
                continue

            if self._username_exclude_replies and toot.is_reply:
                continue
            if self._username_exclude_boosts and toot.is_boost:
                continue

            mail_from = self._factor_mail_from(toot)
            subject = self._factor_mail_subject(toot)
            message = self._factor_mail_message(toot)
            toot_timestamp = self._factor_toot_timestamp(toot)
            attachments = self._factor_toot_attachments(toot)
            # send the mail
            self._send_mail(mail_from, subject, message, toot_timestamp, attachments)
            # remember toot
            self._add_toot_to_toot_state(toot)
            toots_count += 1

        self._logger.info(
            'Processed %s new toot(s) and skipped %s already processed toot(s) for "%s@%s"',
            toots_count, skipped_toots_count, self._username, self._hostname)

    def _get_toots(self):
        account_id = self._get_account_id()
        url = f'api/v1/accounts/{account_id}/statuses'
        toot_dicts = self._request(url, query_params={'limit': self._timeline_limit})
        toots = []
        for toot_dict in toot_dicts:
            toot = Toot(toot_dict)
            toots.append(toot)

        return toots

    def _get_account_id(self):
        uid = self._account_id_by_username.get(self._username)
        if uid:
            account_id = uid.split('@')[0]
        else:
            account = self._request('api/v1/accounts/lookup', query_params={'acct': self._username})
            account_id = account['id']
            uid = f'{account_id}@{self._hostname}'
            self._toot_state[uid] = {'username': self._username, 'toots': []}
            self._account_id_by_username[self._username] = (account_id, self._hostname)

        return account_id

    def _request(self, api_endpoint, query_params=None):
        if not self._hostname:
            raise ValueError('No Mastodon host set!')

        url = urljoin(f'https://{self._hostname}', api_endpoint)
        response = requests.get(url, params=query_params, proxies=self._proxies)
        response.raise_for_status()

        response_json = response.json()
        return response_json

    def _is_toot_already_processed(self, toot):
        uid = self._get_uid(toot)
        user = self._toot_state.get(uid, {})
        user_toots = user.get('toots', [])
        return bool(toot.id in user_toots)

    def _factor_mail_message(self, toot):
        message = MAIL_MESSAGE_TEMPLATE.format(
            toot=self._html2text(toot.content),
            username=self._username,
            posted_by=toot.get_username(compound=False),
            boosted_by=toot.account.username if toot.is_boost else '-',
            in_reply_to_url=self._get_in_reply_to_url(toot),
            videos=self._factor_video_list(toot),
            card=self._factor_card(toot),
            url=toot.url,
            hostname=self._hostname)
        return message

    def _get_in_reply_to_url(self, toot):
        reply_to_id = toot.in_reply_to_id
        if reply_to_id:
            replied_toot = self._request(f'api/v1/statuses/{reply_to_id}')
            if replied_toot:
                return replied_toot['url']

        return '-'

    def _factor_video_list(self, toot):
        videos = ''
        for media in toot.media_attachments:
            if media.type != 'video':
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
            if media.type not in ('image', 'video'):
                continue

            media_url = media.url if media.type == 'image' else media.preview_url

            file_name = Path(media_url).name
            file_content = self._get_image(media_url)
            attachments.append((file_name, file_content))

        return attachments

    def _get_image(self, image_url):
        self._logger.info('Retrieve image "%s"', image_url)
        try:
            response = requests.get(image_url, proxies=self._proxies)
            response.raise_for_status()
        except requests.exceptions.HTTPError as err:
            self._logger.warning('Unable to download image "%s": %s', image_url, err)
            return None
        else:
            return response.content

    def _send_mail(self, mail_from, subject, message, date, files=None):
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

        smtp = smtplib.SMTP(self._mail_server_hostname, self._mail_server_port)
        smtp.sendmail(self._mail_recipient, recipients, msg.as_string())
        smtp.quit()

    def _add_toot_to_toot_state(self, toot):
        uid = self._get_uid(toot)
        user = self._toot_state.setdefault(uid, {'toots': []})
        user['toots'].append(toot.id)

    def _get_uid(self, toot):
        account_id = toot.account.id
        return f'{account_id}@{self._hostname}'

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
