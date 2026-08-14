#!/bin/zsh
export PATH="/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin:$HOME/.local/bin:$PATH"

REPO_ROOT="${BROCKIAN_REPO:-$HOME/Projects/brockian-mathematics}"
PAUSE_FILE="$REPO_ROOT/aristotle/PAUSE_SUBMISSIONS"

if [[ -f "$PAUSE_FILE" ]]; then
  echo "Aristotle submissions paused by $PAUSE_FILE; harvest/verification are unaffected."
  exit 0
fi

set -a
[[ -f "$HOME/.openclaw/vault-bridges.env" ]] && source "$HOME/.openclaw/vault-bridges.env"
set +a
: "${BATCH:=12}"; : "${PACE_S:=5}"; : "${NIGHT_START:=0}"; : "${NIGHT_END:=24}"; : "${NIGHT_CAP:=100000}"
export BATCH PACE_S NIGHT_START NIGHT_END NIGHT_CAP
cd "$REPO_ROOT" || exit 1
exec /opt/homebrew/bin/python3 aristotle/night_submit.py
