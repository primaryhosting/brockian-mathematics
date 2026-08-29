#!/bin/bash
# Deferred independent compile + #print axioms reproduction for the
# Aristotle Waves 16-29 submission. Memory-GATED: refuses to run while the host
# is in critical swap thrash (would not progress and could OOM the machine).
#
# Usage:  bash run-deferred-compile.sh /path/to/aristotle-full-available-corpus-2026-08-29
# Safe to re-run: it compiles into the source dir and rewrites the *.compile.out logs.
set -u
SRC="${1:?pass the corpus bundle dir (contains Wave16.lean etc.)}"
MINFREE_MB="${MINFREE_MB:-900}"          # require >= this many MB free before starting
LEAN="$HOME/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean"
[ -x "$LEAN" ] || { echo "FATAL: lean v4.32.0 not found at $LEAN"; exit 3; }
cd "$SRC" || exit 4
export LEAN_PATH="$SRC"

# --- memory gate ---
free_mb() { echo $(( $(vm_stat | awk '/Pages free/{gsub(/\./,"",$3);print $3}') * 16384 / 1048576 )); }
FM=$(free_mb)
echo "[$(date +%T)] free RAM = ${FM}MB (gate ${MINFREE_MB}MB)"
if [ "$FM" -lt "$MINFREE_MB" ]; then
  echo "ABORT: insufficient free RAM (${FM}MB < ${MINFREE_MB}MB). Free memory (e.g. 'orb stop') and re-run."
  exit 75   # EX_TEMPFAIL — retry later
fi

rm -f ./*.olean ./*.compile.out 2>/dev/null
MODS=(Wave16 Wave17 Wave18 Wave19 Wave20 Wave21 Wave22 Wave23 Wave24 Wave25 Wave26 Wave27 Wave28 Wave29 BookThree BookFour BookThreeFinalAudit BookFourFinalAudit)
FAIL=0
echo "=== COMPILE (pin v4.32.0) $(date +%T) ==="
for m in "${MODS[@]}"; do
  t0=$(date +%s)
  if "$LEAN" -o "$m.olean" "$m.lean" >"$m.compile.out" 2>&1; then
    echo "OK   $m ($(( $(date +%s)-t0 ))s)"
  else
    echo "FAIL $m"; sed 's/^/     /' "$m.compile.out" | head -25; FAIL=1; break
  fi
done
[ $FAIL -ne 0 ] && { echo "=== BUILD FAILED — see *.compile.out ==="; exit 1; }

echo "=== #print axioms REPRODUCTION $(date +%T) ==="
: > AXIOM-FOOTPRINTS.reproduced.txt
for n in 16 17 18 19 20 21 22 23 24 25 26 27 28 29; do
  echo "----- Wave${n}AxiomAudit -----" >> AXIOM-FOOTPRINTS.reproduced.txt
  "$LEAN" "Wave${n}AxiomAudit.lean" >> AXIOM-FOOTPRINTS.reproduced.txt 2>&1
done

# --- footprint sanity: only propext / no-axiom allowed ---
BAD=$(grep "depends on axioms" AXIOM-FOOTPRINTS.reproduced.txt | grep -v "\[propext\]" | wc -l | tr -d ' ')
NO=$(grep -c "does not depend on any axioms" AXIOM-FOOTPRINTS.reproduced.txt)
PX=$(grep -c "depends on axioms: \[propext\]" AXIOM-FOOTPRINTS.reproduced.txt)
echo "=== REPRODUCED FOOTPRINTS: no_axiom=$NO propext_only=$PX non_standard=$BAD ==="
if [ "$BAD" -ne 0 ]; then
  echo "!!! FINDING: non-standard axiom(s) detected — corpus is NOT axiom-honest:"
  grep "depends on axioms" AXIOM-FOOTPRINTS.reproduced.txt | grep -v "\[propext\]"
fi
echo "=== DONE $(date +%T) — build=GREEN, footprints in AXIOM-FOOTPRINTS.reproduced.txt ==="
echo "Update ARISTOTLE-ATTESTATION.{md,json}: set compile_result=OK per file and replace"
echo "the VENDOR-CLAIMED footprint block with these reproduced counts (no_axiom=$NO propext=$PX nonstd=$BAD)."
