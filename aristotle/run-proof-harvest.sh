#!/bin/zsh
# Wrapper for the Aristotle proof-harvest launchd agent.
# Sources the vault for the two Aristotle API keys, then harvests + emails.
export PATH="/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin:$HOME/.local/bin:$PATH"
set -a
[ -f "$HOME/.openclaw/vault-bridges.env" ] && source "$HOME/.openclaw/vault-bridges.env"
set +a
: "${SOLVER_NOTIFY_TO:=chrisbrock54@gmail.com}"
export SOLVER_NOTIFY_TO
cd "$HOME/Projects/brockian-mathematics" || exit 1
exec /opt/homebrew/bin/python3 aristotle/harvest_proofs.py
