#!/bin/zsh
export PATH="/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin:$HOME/.local/bin:$PATH"
set -a
[ -f "$HOME/.openclaw/vault-bridges.env" ] && source "$HOME/.openclaw/vault-bridges.env"
set +a
: "${BATCH:=12}"; : "${PACE_S:=5}"; : "${NIGHT_START:=0}"; : "${NIGHT_END:=24}"; : "${NIGHT_CAP:=100000}"
export BATCH PACE_S NIGHT_START NIGHT_END NIGHT_CAP
cd "$HOME/Projects/brockian-mathematics" || exit 1
exec /opt/homebrew/bin/python3 aristotle/night_submit.py
