#!/usr/bin/env bash
# verify.sh — the full honesty gate, as one command.
#
# Everything a change to the registry, the attestations, or the engine must pass. This is
# the single source of "is the repository honest right now". All checks are LOCAL (no AXLE
# calls needed for the gate itself; the test suite sources the vault only if present).
#
#   scripts/verify.sh
#
set -euo pipefail
cd "$(dirname "$0")/.."

if [ -f "$HOME/.openclaw/vault-bridges.env" ]; then
  set -a; source "$HOME/.openclaw/vault-bridges.env"; set +a
fi

echo "== 1/3  engine.audit --strict =="
echo "        (registry consistency + overclaim firewall + no-theater + attestation integrity)"
python3 -m engine.audit --strict

echo
echo "== 2/3  registry freshness =="
echo "        (registry/theorems.json is byte-identical to gen_registry output)"
python3 scripts/check_registry_fresh.py

echo
echo "== 3/3  test suite =="
python3 -m pytest tests/ aristotle/tests/ pipeline/tests/ -q

echo
echo "ALL GATES PASS"
