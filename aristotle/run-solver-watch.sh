#!/bin/zsh
# Wrapper for the Aristotle solver-watch launchd agent.
# Sources the vault for the two Aristotle API keys, then polls + stages notices.
# Email delivery is off unless SOLVER_NOTIFY_EMAIL is explicitly enabled.
export PATH="/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin:$HOME/.local/bin:$PATH"
set -a
[ -f "$HOME/.openclaw/vault-bridges.env" ] && source "$HOME/.openclaw/vault-bridges.env"
set +a
: "${SOLVER_NOTIFY_TO:=chrisbrock54@gmail.com}"
: "${SOLVER_NOTIFY_EMAIL:=0}"
export SOLVER_NOTIFY_TO
export SOLVER_NOTIFY_EMAIL
cd "$HOME/Projects/brockian-mathematics" || exit 1
exec /opt/homebrew/bin/python3 aristotle/solver_watch.py
