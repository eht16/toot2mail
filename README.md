# Toot2Mail

Generate notification emails from Mastodon toots.

Configure Mastodon accounts you want to follow and receive notification
emails for toots in the monitored accounts.

This can be used to passively follow Mastodon accounts without having to subscribe yourself.

It works completely by using the public interface APIs of Mastodon.

## Installation and setup

Toot2Mail requires Python 3.9 or newer.
Clone the GIT repository and start the script `toot2mail.py`, ideally on a regular
basis e.g. as cronjob.

The following requirements must be installed:
requests and requests-html.

Before using Toot2Mail, you need to create a configuration file called `toot2mail.conf`.
Toot2Mail will search for `toot2mail.conf` in the following locations (in that order):

  - ~/.config/toot2mail.conf
  - toot2mail.conf (in current working directory)

An example configuration file can be found in the sources or online
at https://raw.githubusercontent.com/eht16/toot2mail/master/toot2mail.conf.example.

For details on the configuration options, consider the comments in the
example configuration file.

## Disclaimer

Use this tool at your own risk only.
There is no warranty at all.

## Author

Enrico Tröger <enrico.troeger@uvena.de>
