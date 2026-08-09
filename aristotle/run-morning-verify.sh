#!/bin/zsh
export PATH="/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin:$HOME/.local/bin:$PATH"
set -a
[ -f "$HOME/.openclaw/vault-bridges.env" ] && source "$HOME/.openclaw/vault-bridges.env"
set +a
: "${SOLVER_NOTIFY_TO:=chrisbrock54@gmail.com}"; export SOLVER_NOTIFY_TO
cd "$HOME/Projects/brockian-mathematics" || exit 1
# don't stack: skip if a verify is already grinding
if pgrep -f verify_stage.py >/dev/null; then echo "verify_stage already running; harvest only"; /opt/homebrew/bin/python3 aristotle/harvest_proofs.py; exit 0; fi
/opt/homebrew/bin/python3 aristotle/harvest_proofs.py
/opt/homebrew/bin/python3 aristotle/verify_stage.py
/opt/homebrew/bin/python3 aristotle/select_best.py
/opt/homebrew/bin/python3 aristotle/catalogue_domains.py
/opt/homebrew/bin/python3 aristotle/lemma_mine.py
/opt/homebrew/bin/python3 aristotle/reduction_tracker.py
CROSS_MAX=6 /opt/homebrew/bin/python3 aristotle/cross_check.py
/opt/homebrew/bin/python3 aristotle/observatory.py

