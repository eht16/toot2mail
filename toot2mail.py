#!/usr/bin/env python3
#
# This software may be modified and distributed under the terms
# of the MIT license.  See the LICENSE file for details.

from argparse import ArgumentParser
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
import re
import smtplib
import socket
import sys
import textwrap
import urllib3

import markdownify
import requests
from PIL import Image, ImageDraw

HTTP_USER_AGENT = 'Mozilla/5.0 (Windows NT 10.0; rv:128.0) Gecko/20100101 Firefox/128.0'
CONFIG_FILENAME = '~/.config/toot2mail.conf'
MAIL_MESSAGE_TEMPLATE = '''{toot}

{card}
--------------------------------
Videos: {videos}
Posted by: {posted_by}
Boosted by: {boosted_by}
Application: {application}

In Reply To: {in_reply_to_url}
URL: {url}
Timeline: https://{hostname}/@{username}/with_replies
Toot ID: {toot_id}
'''

CARD_TEMPLATE = '''
--------------------------------
Card URL:   {card_url}:
Card Title: {card_title}'''


INCOMPATIBLE_ACTIVITY_PUB_INSTANCES = (
    'akkoma',
    'firefish',
    'friendica',
    'gotosocial',
    'mammuthus (experimental)',
    'mitra',
    'pixelfed',
    'peertube',
)


# Based on Mastodon.py's AttribAccessDict
# (https://github.com/halcy/Mastodon.py/blob/master/mastodon/types_base.py)
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
    def application(self):
        application = self.get('application')
        return AttribAccessDict(application or {})

    @property
    def content(self):
        content = self.get('content')
        spoiler_text = self.get('spoiler_text')
        if spoiler_text:
            return f'{spoiler_text}\n\n{content}'

        return content

    @property
    def card(self):
        card = self.reblog.card if self.is_boost else self.get('card')
        return AttribAccessDict(card or {})

    @property
    def reblog(self):
        return Toot(self.get('reblog') or {})

    @property
    def account(self):
        account = self.get('account')
        return AttribAccessDict(account or {})

    def get_hostname(self):
        parsed_url = urlsplit(self.url)
        return parsed_url.netloc

    def get_uid(self):
        acct = self.account.acct
        if '@' in acct:
            return acct.lower()

        username_lowercase = self.account.username.lower()
        hostname_lowercase = self.get_hostname().lower()
        return f'{username_lowercase}@{hostname_lowercase}'

    def get_username(self, compound=True):
        if self.is_boost:
            if compound:
                return f'{self.account.username}: {self.reblog.account.username}'

            return self.reblog.account.username

        return self.account.username

    def get_display_name(self, compound=True):
        display_name = self.account.display_name or self.account.username
        if self.is_boost:
            if compound:
                reblog_display_name = self.reblog.account.display_name or self.reblog.account.username
                return f'{display_name}: {reblog_display_name}'

            return display_name

        return display_name

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
        self._hashtags = None
        self._references = None
        self._toot_state = None
        self._content_replacements = {}
        self._cache = {}  # simple local instance cache for HTTP requests

    def process(self, toot_reference=None, tag_reference=None, user_reference=None):
        self._setup_config()
        self._setup_logger()
        self._log_hello()
        self._assert_not_already_running()
        self._write_lock()

        self._read_toot_state()
        try:
            if toot_reference:
                self._process_single_toot(toot_reference)
            elif tag_reference:
                hashtag, hostname = tag_reference.split('@')
                self._process_hashtag(hashtag, hostname)
            elif user_reference:
                username, hostname = user_reference.split('@')
                self._process_user(username, hostname, False, False)
            else:
                for username, hostname, exclude_replies, exclude_boosts in self._usernames:
                    self._process_user(username, hostname, exclude_replies, exclude_boosts)
                    self._pause()
                for hashtag, hostname in self._hashtags:
                    self._process_hashtag(hashtag, hostname)
                    self._pause()
        finally:
            self._write_toot_state()
            self._remove_lock()

        self._log_farewell()

    def _setup_config(self):
        config_parser = ConfigParser(allow_no_value=True, delimiters=('=',))
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

        for regex, replacement in config_parser.items('content_replacement', raw=True):
            self._content_replacements[regex] = replacement

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

        self._hashtags = []
        for uid, flags in config_parser.items('hashtags'):
            hashtag, hostname = uid.split('@')
            self._hashtags.append((hashtag, hostname))

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

    def _process_single_toot(self, toot_reference):
        toot_id, hostname = toot_reference.split('@')
        toot_dict = self._request(f'api/v1/statuses/{toot_id}', hostname)
        toot = Toot(toot_dict)
        self._process_toot(toot)
        self._logger.info('Processed toot(s) for %s@%s', toot.id, toot.get_hostname())

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

                self._process_toot(toot)
                toots_count += 1

            self._logger.info(
                'Processed %s new toot(s) and skipped %s already processed toot(s) for "%s@%s"',
                toots_count, skipped_toots_count, username, hostname)
        except Exception as exc:
            log_func = self._logger.exception
            if self._is_exception_timeout(exc):
                log_func = self._logger.warning
            log_func('An error occurred while processing "%s@%s": %s', username, hostname, exc)

    def _is_exception_timeout(self, exc):
        if isinstance(exc, (TimeoutError, requests.exceptions.RequestException)):
            exc_message = str(exc)
            if 'timed out' in exc_message or 'TimeoutError' in exc_message:
                return True
        return False

    def _get_toots(self, username, hostname):
        account_id = self._get_account_id(username, hostname)
        url = f'api/v1/accounts/{account_id}/statuses'
        toot_dicts = self._request(url, hostname, query_params={'limit': self._timeline_limit})
        toots = [Toot(toot_dict) for toot_dict in toot_dicts]
        return toots

    def _get_account_id(self, username, hostname):
        account = self._request('api/v1/accounts/lookup', hostname, query_params={'acct': username})
        return account['id']

    def _request(self, api_endpoint, hostname, query_params=None, url=None):
        if not hostname and not url:
            raise ValueError('No Mastodon instance set!')

        if url:
            cache_key = (url, str(query_params))
        else:
            cache_key = (hostname, api_endpoint, str(query_params))
        result = self._cache.get(cache_key, '__no_cache_result__')
        if result != '__no_cache_result__':
            return result

        if not url:
            url = urljoin(f'https://{hostname}', api_endpoint)

        response = requests.get(url, params=query_params, proxies=self._proxies,
                                timeout=self._timeout,
                                headers={'User-Agent': HTTP_USER_AGENT})
        response.raise_for_status()

        response_json = response.json()
        self._cache[cache_key] = response_json
        return response_json

    def _is_toot_already_processed(self, toot):
        uid = toot.get_uid()
        toot_uri = toot.uri.lower()
        user = self._toot_state.get(uid, {})
        user_toots = user.get('toots', [])
        return bool(toot_uri in user_toots)

    def _process_toot(self, toot):
        self._references = set()
        try:
            # re-request the toot from the originating instance to get their account and status ids
            toot = self._get_original_toot(toot)

            self._get_toot_in_reply_to(toot)
            text_content = self._factor_text_content(toot)
            mail_from = self._factor_mail_from(toot)
            subject = self._factor_mail_subject(text_content)
            message = self._factor_mail_message(toot, text_content)
            toot_timestamp = self._factor_toot_timestamp(toot)
            attachments = self._factor_toot_attachments(toot)
            headers = self._factor_mail_headers(toot)
            # send the mail
            self._send_mail(mail_from, subject, message, toot_timestamp, attachments, headers)
            # remember toot
            self._add_toot_to_toot_state(toot)
        except Exception as exc:
            log_func = self._logger.exception
            if self._is_exception_timeout(exc):
                log_func = self._logger.warning
            log_func('An error occurred while processing "%s@%s" at toot %s: %s',
                     toot.account.username, toot.get_hostname(), toot.id, exc)

    def _get_toot_instance_type(self, hostname):
        nodeinfo_url = None
        try:
            response = self._request('.well-known/nodeinfo', hostname)
        except (urllib3.exceptions.MaxRetryError, requests.exceptions.ProxyError,
                requests.exceptions.HTTPError) as exc:
            self._logger.info('Error on querying node info from %s: %s', hostname, exc)
            return None, None

        for link in response.get('links', []):
            if link.get('rel') == 'http://nodeinfo.diaspora.software/ns/schema/2.0':
                nodeinfo_url = link.get('href')
                break

        if nodeinfo_url:
            try:
                nodeinfo = self._request(api_endpoint=None, hostname=None, url=nodeinfo_url)
            except (urllib3.exceptions.MaxRetryError, requests.exceptions.ProxyError,
                    requests.exceptions.HTTPError) as exc:
                self._logger.info('Error on querying node info from %s: %s', nodeinfo_url, exc)
                return None, None

            software_name = nodeinfo.get('software', {}).get('name', 'unknown')
            software_name = software_name.lower()
            software_version = nodeinfo.get('software', {}).get('version', 'unknown')
            return software_name, software_version

        return None, None

    def _get_original_toot(self, toot):
        parsed_url = urlsplit(toot.url)
        originating_hostname = parsed_url.netloc
        # this probably won't work for other services than Mastodon
        originating_toot_id = parsed_url.path.split('/')[-1]  # TODO make this robust

        try:
            new_toot = self._request(f'api/v1/statuses/{originating_toot_id}', originating_hostname)
            return Toot(new_toot)
        except (urllib3.exceptions.MaxRetryError, requests.exceptions.ProxyError) as exc:
            self._logger.info('Originating toot with ID "%s" on instance "%s" could '
                              'not be retrieved: %s',
                              originating_toot_id, originating_hostname, exc)
        except requests.exceptions.HTTPError as exc:
            # ignore errors and fall back to the previously retrieved instance local toot
            if exc.response.status_code in (403, 404):
                self._logger.info('Originating toot with ID "%s" on instance "%s" could '
                                  'not be retrieved (%s): %s',
                                  originating_toot_id, originating_hostname,
                                  exc.response.status_code, exc)
            else:
                raise

        return toot

    def _can_toot_be_processed(self, toot):
        software_name = toot.get('software_name')
        if software_name is None:
            software_name, software_version = self._get_toot_instance_type(toot.get_hostname())
            toot['software_name'] = software_name
            toot['software_version'] = software_version

        if software_name in INCOMPATIBLE_ACTIVITY_PUB_INSTANCES:
            # ignore toots from instances which do not offer a Mastodon like API
            self._logger.info('Toot retrieval with ID "%s" on instance "%s" skipped '
                              'because incompatible instance software: %s %s',
                              toot.id, toot.get_hostname(),
                              toot.get('software_name'), toot.get('software_version'))
            return False

        return True

    def _get_toot_in_reply_to(self, toot):
        if toot.in_reply_to_id:
            if not self._can_toot_be_processed(toot):
                return

            try:
                in_reply_to = self._request(f'api/v1/statuses/{toot.in_reply_to_id}', toot.get_hostname())
            except requests.exceptions.HTTPError as exc:
                # ignore 404 errors, sometimes toots might get deleted
                if exc.response.status_code == 404:
                    self._logger.info('Toot reply "%s" could not be found on server (404): %s',
                                      toot.in_reply_to_id, exc)
                    return
                # raise for all other errors
                raise

            if in_reply_to:
                toot.in_reply_to = Toot(in_reply_to)
                # re-request the toot from the originating instance to get account and status ids
                if self._can_toot_be_processed(toot):
                    toot.in_reply_to = self._get_original_toot(toot.in_reply_to)

                if not self._is_toot_already_processed(toot.in_reply_to):
                    self._process_toot(toot.in_reply_to)

    def _factor_mail_message(self, toot, text_content):
        posted_by_username = toot.get_username(compound=False)
        posted_by_display_name = toot.get_display_name(compound=False)
        posted_by = f'{posted_by_display_name} (@{posted_by_username})'

        if toot.is_boost:
            boosted_by = f'{toot.account.display_name} (@{toot.account.username})'
        else:
            pass

        if toot.application:
            application = f'{toot.application.name}'
            if toot.application.website:
                application = f'{application} ({toot.application.website})'
        else:
            application = '-'

        message = MAIL_MESSAGE_TEMPLATE.format(
            toot=text_content,
            username=toot.account.username,
            posted_by=posted_by,
            boosted_by=boosted_by,
            in_reply_to_url=toot.in_reply_to.url if toot.is_reply and toot.in_reply_to else '-',
            videos=self._factor_video_list(toot),
            card=self._factor_card(toot),
            url=toot.reblog.url if toot.is_boost else toot.url,
            toot_id=toot.id,
            application=application,
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
            card_url = self._perform_content_replacements(card.url)
            return CARD_TEMPLATE.format(card_url=card_url, card_title=card.title)

        return ''

    def _factor_mail_from(self, toot):
        encoded_name = Header(toot.get_display_name(), 'utf-8').encode()
        return f'{encoded_name} <{self._mail_from}>'

    def _factor_mail_subject(self, text_content):
        if len(text_content) > self._mail_maximum_subject_length:
            text_content = text_content[:self._mail_maximum_subject_length] + '...'

        return Header(text_content or '...', 'utf-8')

    def _factor_text_content(self, toot):
        text_content = self._html2text(toot.content)
        text_content = self._perform_content_replacements(text_content)

        return text_content

    def _html2text(self, html):
        if not html:
            return html

        return markdownify.markdownify(html, strip=['a'],
                                       escape_asterisks=False, escape_underscores=False).strip()

    def _perform_content_replacements(self, content):
        if not content:
            return content

        for pattern, replacement in self._content_replacements.items():
            content = re.sub(pattern, replacement, content)

        return content

    def _factor_toot_timestamp(self, toot):
        toot_created_at = toot.created_at
        if toot_created_at.endswith('Z') and sys.version_info < (3, 11):
            toot_created_at = toot_created_at[:-1]  # strip TZ info, Python < 3.11 cannot handle it

        created_at = datetime.fromisoformat(toot_created_at)
        return created_at.timestamp()

    def _factor_toot_attachments(self, toot):
        attachments = []
        hostname = toot.get_hostname()
        # card image
        card = toot.card
        if card and card.image:
            file_name = f'card_{Path(card.image).name}'
            file_name, file_content = self._get_image(card.image, file_name, hostname)
            attachments.append((file_name, file_content))

        # media attachments
        for media in toot.media_attachments:
            if media.type not in ('gifv', 'image', 'video'):
                continue

            media_url = media.url if media.type == 'image' else media.preview_url

            file_name = Path(media_url).name
            file_name, file_content = self._get_image(media_url, file_name, hostname)
            attachments.append((file_name, file_content))

        return attachments

    def _get_image(self, image_url, file_name, hostname):
        self._logger.info('Retrieve image "%s"', image_url)
        try:
            response = requests.get(image_url, proxies=self._proxies, timeout=self._timeout,
                                    headers={'User-Agent': HTTP_USER_AGENT,
                                             'Referer': f'https://{hostname}'})

            response.raise_for_status()
        except requests.exceptions.HTTPError as err:
            msg = f'Unable to download image "{image_url}": {err}'
            self._logger.warning(msg)
            # generate an image containing the error message to indicate there was
            # an image which could not be loaded
            image_data = self._generate_download_error_image(msg)
            file_name = f'{file_name}.png'
        else:
            image_data = self._downscale_image(response.content)

        return file_name, image_data

    def _generate_download_error_image(self, text):
        if self._image_maximum_size:
            width = self._image_maximum_size[0]
            height = self._image_maximum_size[1]
        else:
            width = 500
            height = 300

        max_text_width = int(width / 10)
        wrapped_text = textwrap.wrap(text, width=max_text_width)

        image = Image.new(mode="RGB", size=(width, height), color='lightgrey')
        draw = ImageDraw.Draw(image)
        for i, line in enumerate(wrapped_text):
            draw.text((25, 25 + (i * 20)), line, fill='black')

        result = io.BytesIO()
        image.save(result, 'PNG')
        return result.getvalue()

    def _downscale_image(self, image_data):
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
                   'Message-ID': f'<{toot.account.username}.{hostname}.{toot.id}@{fqdn}>'}
        if toot.is_reply and toot.in_reply_to:
            in_reply_to_hostname = toot.in_reply_to.get_hostname()
            headers['In-Reply-To'] = f'<{toot.in_reply_to.account.username}.{in_reply_to_hostname}.' \
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
        toot_uri = toot.uri.lower()
        user = self._toot_state.setdefault(uid, {'toots': []})
        user['toots'].append(toot_uri)

    def _process_hashtag(self, hashtag, hostname):
        try:
            self._logger.info('Processing new toots for "#%s@%s"', hashtag, hostname)

            toots_count = 0
            skipped_toots_count = 0
            toots = self._get_toots_for_hashtag(hashtag, hostname)
            for toot in toots:
                if self._is_toot_already_processed(toot):
                    skipped_toots_count += 1
                    continue

                self._process_toot(toot)
                toots_count += 1

            self._logger.info(
                'Processed %s new toot(s) and skipped %s already processed toot(s) for "#%s@%s"',
                toots_count, skipped_toots_count, hashtag, hostname)
        except Exception as exc:
            log_func = self._logger.exception
            if self._is_exception_timeout(exc):
                log_func = self._logger.warning
            log_func('An error occurred while processing "#%s@%s": %s', hashtag, hostname, exc)

    def _get_toots_for_hashtag(self, hashtag, hostname):
        url = f'api/v1/timelines/tag/{hashtag}'
        toot_dicts = self._request(url, hostname, query_params={'limit': self._timeline_limit})
        toots = [Toot(toot_dict) for toot_dict in toot_dicts]
        return toots

    def _pause(self):
        sleep(randint(3, 10))

    def _write_toot_state(self):
        with open(self._state_file_path, 'w', encoding='utf-8') as state_file:
            json.dump(self._toot_state, state_file, indent=2)

    def _remove_lock(self):
        self._lock_file_path.unlink()


def main():
    argument_parser = ArgumentParser()
    exclusive_group = argument_parser.add_mutually_exclusive_group()
    exclusive_group.add_argument('-s', '--toot', dest='toot_reference',
                                 help='Process a single Toot, specified as <id>@<instance.tld>')
    exclusive_group.add_argument('-t', '--tag', dest='tag',
                                 help='Process a given tag, specified as <tag>@<instance.tld>')
    exclusive_group.add_argument('-u', '--user', dest='user',
                                 help='Process a given user, specified as <user>@<instance.tld>')
    arguments = argument_parser.parse_args()

    processor = MastodonEmailProcessor()
    processor.process(toot_reference=arguments.toot_reference, tag_reference=arguments.tag,
                      user_reference=arguments.user)


if __name__ == '__main__':
    main()
