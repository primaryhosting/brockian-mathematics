#!/bin/zsh
# sync_to_gdrive.sh — mirror the Brockian proof corpus + solver artifacts into Google Drive
# so the whole store (PROVED modules, registry, attestations, raw Aristotle solver output,
# submission/harvest ledgers, and the consolidated tier-labeled datastore) is preserved
# off-machine and can be handed to an AI for at-scale analysis later.
#
# Additive by design: rsync WITHOUT --delete (never removes what's already in Drive).
# The huge raw-candidate dir is shipped as ONE tarball (FUSE handles one big file far
# better than 4000+ tiny ones).  Run standalone or from the harvest-sync agent.
export PATH="/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin:$HOME/.local/bin:$PATH"
set -u
REPO="$HOME/Projects/brockian-mathematics"
DEST="$HOME/Library/CloudStorage/GoogleDrive-admin@primary.hosting/My Drive/Brockian-Math-Corpus"
LOG="$REPO/aristotle/gdrive_sync.log"
log(){ echo "$(date '+%Y-%m-%dT%H:%M:%S') $*" | tee -a "$LOG"; }

cd "$REPO" || exit 1
[ -d "$HOME/Library/CloudStorage/GoogleDrive-admin@primary.hosting" ] || { log "FATAL: GDrive not mounted"; exit 1; }
mkdir -p "$DEST/registry" "$DEST/solver_ledgers"

log "=== sync start ==="

# 1. Consolidated, honest, tier-labeled datastore (best single artifact for AI analysis)
python3 scripts/export_aristotle_datastore.py >/dev/null 2>&1 \
  && cp -f torus/public/aristotle-datastore.json "$DEST/aristotle-datastore.json" 2>/dev/null \
  && log "datastore exported + copied" || log "datastore export skipped/failed (non-fatal)"

# 2. Clean corpus: PROVED Lean modules, the registry truth, attestations, BV targets
rsync -a --no-perms --no-owner --no-group Brockian/            "$DEST/Brockian/"            2>>"$LOG" && log "Brockian/ synced"
rsync -a --no-perms --no-owner --no-group registry/attestations/ "$DEST/registry/attestations/" 2>>"$LOG" && log "attestations synced"
cp -f registry/theorems.json "$DEST/registry/theorems.json" 2>/dev/null
cp -f registry/REGISTRY.md   "$DEST/registry/REGISTRY.md"   2>/dev/null
[ -d targets ] && rsync -a --no-perms --no-owner --no-group targets/ "$DEST/targets/" 2>>"$LOG" && log "targets/ synced"

# 3. Solver access + ledgers (who solved what, submission ids, harvest state)
for f in submitted_night.json harvest_ledger.json solver_manifest.json frontier_queue.json \
         solver_notification_outbox.jsonl submitted_ids.json axle_verify.json axle_axiom_audit.json; do
  [ -f "aristotle/$f" ] && cp -f "aristotle/$f" "$DEST/solver_ledgers/$f" 2>/dev/null
done
log "solver ledgers copied"

# 4. Raw Aristotle candidate proofs — one tarball (4000+ files ship cleanly as one object)
if [ -d aristotle/harvest_100 ]; then
  tar -czf "/tmp/harvest_100_candidates.tar.gz" -C aristotle harvest_100 2>>"$LOG" \
    && mv -f "/tmp/harvest_100_candidates.tar.gz" "$DEST/harvest_100_candidates.tar.gz" \
    && log "harvest_100 tarball ($(ls aristotle/harvest_100 | wc -l | tr -d ' ') files) synced"
fi
[ -d aristotle/best_proofs ] && tar -czf "/tmp/best_proofs.tar.gz" -C aristotle best_proofs 2>>"$LOG" \
  && mv -f "/tmp/best_proofs.tar.gz" "$DEST/best_proofs.tar.gz" && log "best_proofs tarball synced"

# 5. README manifest with live counts
PROVED=$(python3 -c "import json;d=json.load(open('registry/theorems.json'));print(sum(1 for t in (d if isinstance(d,list) else d.get('theorems',[])) if t.get('register')=='PROVED'))" 2>/dev/null)
TARGETS=$(python3 -c "import json;print(len(json.load(open('aristotle/submitted_night.json'))))" 2>/dev/null)
cat > "$DEST/README.md" <<EOF
# Brockian Mathematics — Proof Corpus & Solver Store
_Last synced: $(date '+%Y-%m-%d %H:%M:%S %Z')_

Off-machine mirror of the Brockian math program. Additive (never deletes).

- **aristotle-datastore.json** — consolidated, tier-labeled proof store (best single
  file for AI-at-scale analysis). Every proof carries an honest tier:
  AXLE_VERIFIED_AXIOM_CLEAN (the only PROVED tier) / AXLE_VERIFIED / ARISTOTLE_CANDIDATE.
- **registry/theorems.json** — the truth: ${PROVED:-?} PROVED entries. **registry/attestations/** — per-module AXLE verdicts.
- **Brockian/** — all PROVED Lean 4 modules (source).
- **targets/** — Bombieri–Vinogradov layered work (statement-first, not in PROVED corpus).
- **solver_ledgers/** — submitted_night.json (${TARGETS:-?} targets, both Aristotle accounts, with project ids),
  harvest_ledger.json, solver_manifest.json (what each solver solves), frontier_queue.json (open goals).
- **harvest_100_candidates.tar.gz** — every raw sorry-free Aristotle candidate (pre-verification).
- **best_proofs.tar.gz** — deduped best proof per target.

Repo: primaryhosting/brockian-mathematics. Verification: AXLE (axle.axiommath.ai, env lean-4.32.2).
EOF
log "README written (PROVED=${PROVED:-?}, targets=${TARGETS:-?})"
log "=== sync done ==="
