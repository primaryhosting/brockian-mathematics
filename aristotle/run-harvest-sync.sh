#!/bin/zsh
# run-harvest-sync.sh — the wired harvester.
# 1. Pull EVERY finished (IDLE) Aristotle job on both accounts into harvest_100/
#    (harvest_all.py: read-only against Aristotle, resumable, skips already-harvested).
# 2. Mirror the refreshed corpus + solver artifacts to Google Drive.
# Runs on an interval via ai.brockian.harvest-sync; also safe to run by hand.
export PATH="/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin:$HOME/.local/bin:$PATH"
set -a
[ -f "$HOME/.openclaw/vault-bridges.env" ] && source "$HOME/.openclaw/vault-bridges.env"
set +a
: "${SOLVER_NOTIFY_TO:=chrisbrock54@gmail.com}"
export SOLVER_NOTIFY_TO
cd "$HOME/Projects/brockian-mathematics" || exit 1

# Pull finished jobs (both keyed-by-uuid and any direct-to-Aristotle jobs).
/opt/homebrew/bin/python3 aristotle/harvest_proofs.py 2>&1
HARVEST_ALL_MAX=80 /opt/homebrew/bin/python3 aristotle/harvest_all.py 2>&1

# Honest AXLE triage (records True/False verdicts in axle_verify.json; NEVER mutates the
# registry — that stays the clean-engine's job via attest.py + gen_registry). Bounded per
# cycle so it clears the candidate backlog gradually and flags genuine compiles. A sorry-free
# candidate is NOT a proof: many "solved" open-problem candidates fail this AXLE leg.
/opt/homebrew/bin/python3 aristotle/select_best.py 2>&1
AXLE_MAX=25 /opt/homebrew/bin/python3 aristotle/axle_verify.py 2>&1

# Push everything off-machine (additive) — corpus, ledgers, and the refreshed AXLE verdicts.
exec /bin/zsh "$HOME/Projects/brockian-mathematics/scripts/sync_to_gdrive.sh"
