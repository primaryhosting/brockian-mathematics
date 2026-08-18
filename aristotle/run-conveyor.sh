#!/bin/zsh
# Wrapper for the Aristotle Conveyor launchd agent (ai.brockian.conveyor).
# Sources the vault for the Aristotle API keys (pattern: run-solver-watch.sh),
# then runs ONE short-lived conveyor cycle and exits — never a resident daemon.
# Heavy verify/attest work only happens when new candidates exist since the
# cursor; caps mirror run-morning-verify.sh (AXLE_MAX, HARVEST_ALL_MAX).
export PATH="/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin:$HOME/.local/bin:$PATH"
set -a
[ -f "$HOME/.openclaw/vault-bridges.env" ] && source "$HOME/.openclaw/vault-bridges.env"
set +a
: "${SOLVER_NOTIFY_TO:=chrisbrock54@gmail.com}"
: "${SOLVER_NOTIFY_EMAIL:=0}"   # daily-digest email is OPT-IN; outbox + Today tile are primary
: "${AXLE_MAX:=120}"
: "${HARVEST_ALL_MAX:=80}"
: "${CROSS_MAX:=6}"
: "${CONVEYOR_VERIFY_BUDGET:=900}"
export SOLVER_NOTIFY_TO SOLVER_NOTIFY_EMAIL AXLE_MAX HARVEST_ALL_MAX CROSS_MAX CONVEYOR_VERIFY_BUDGET
# Lovable manager bearer token: read from the manager's own launchd plist so
# /queue-submit auth always matches what the manager accepts. Never printed.
if [ -z "$OPENCLAW_AUTH_TOKEN" ]; then
  _lm_plist="$HOME/Library/LaunchAgents/ai.openclaw.lovable-manager.plist"
  if [ -f "$_lm_plist" ]; then
    OPENCLAW_AUTH_TOKEN=$(/usr/libexec/PlistBuddy -c \
      "Print :EnvironmentVariables:OPENCLAW_AUTH_TOKEN" "$_lm_plist" 2>/dev/null)
    [ -n "$OPENCLAW_AUTH_TOKEN" ] && export OPENCLAW_AUTH_TOKEN
  fi
fi
cd "$HOME/Projects/brockian-mathematics" || exit 1
exec /opt/homebrew/bin/python3 aristotle/conveyor.py
