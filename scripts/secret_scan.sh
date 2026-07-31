#!/usr/bin/env bash
# Pre-publish secret scan (spec §8). Scans working tree + full git history for key
# patterns. Exit non-zero on any hit — publication is gated on this passing.
set -euo pipefail
cd "$(dirname "$0")/.."

# Match actual secret VALUES, not variable names mentioned in docs. Env-var assignments
# must be followed by 16+ chars of real value (a bare `NAME=` in prose won't match).
PATTERNS='sk-[A-Za-z0-9]{20}|sb_secret_[A-Za-z0-9]{10}|(AXLE|ARISTOTLE)_API_KEY=[A-Za-z0-9_-]{16,}|eyJ[A-Za-z0-9_-]{30,}\.[A-Za-z0-9_-]{20,}|-----BEGIN [A-Z ]*PRIVATE KEY-----'

hits=0
echo "== working tree =="
if git grep -nIE "$PATTERNS" -- . ':!scripts/secret_scan.sh' 2>/dev/null; then hits=1; fi
echo "== full history =="
# scan every blob in history (diff text), excluding this scanner
if git log -p --all -- . ':!scripts/secret_scan.sh' 2>/dev/null | grep -nIE "$PATTERNS" ; then hits=1; fi

if [ "$hits" -ne 0 ]; then
  echo "SECRET SCAN: FAIL — potential secret found; do NOT publish." >&2
  exit 1
fi
echo "SECRET SCAN: clean ✓"
