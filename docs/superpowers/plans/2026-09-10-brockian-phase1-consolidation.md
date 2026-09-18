# Brockian Phase 1 — GitHub Consolidation Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Move `origin/main` of `primaryhosting/brockian-mathematics` from its stale 2026-08-27 state to the current, honest, consolidated state (≈12,373 PROVED, KG v3 graph, NS/Euler specs, ~47 new proofs, refreshed attestations) by landing a consolidation branch through the existing `promotion-gate` CI — losing nothing and committing no secrets.

**Architecture:** This is a **git-operations runbook**, not a code-authoring plan. The "tests" are the repo's own gate scripts (`gen_registry.py` derive-diff, `check_attestation_integrity.py`, `audit_registry_consistency.py`, `verify_firewall.py`, `validate_manifests.py`, the control-plane pytest set) run first locally (dry-run) and then in CI on the PR. We merge two divergent lines — `snapshot/brockian-dirty-2026-08-29` (content superset of `conveyor`+`codex`) and `origin/main` (5 governance commits) — into `consolidate/2026-09-10`, resolving conflicts by a deterministic policy (governance files ← origin, content ← snapshot), then PR into `main`.

**Tech Stack:** git, `gh` CLI, `gitleaks`, Python 3 gate scripts, GitHub Actions `promotion-gate`.

**Spec:** `docs/superpowers/specs/2026-09-10-brockian-sharing-system-design.md`

**⚠️ Safety invariants (hold for the whole plan):**
- Never force-push `main`. Land only via PR through green CI.
- A secrets-scan hit is a HARD STOP → surface to human, do not commit/push.
- Keep ≥15 GB disk free; a 20k-file push has spiked this machine to 100% before.
- The `pre-consolidation-2026-09-10` tag + bundle (Task 1) is the rollback path — create it before any history changes.
- Registry files are regenerated mechanically, never hand-edited.

---

## Chunk 1: Consolidation runbook (Tasks 1–6)

### Task 1: Pre-flight safety gate (U1)

**Files:**
- Create: `~/brockian-pre-consolidation-2026-09-10.bundle` (rollback bundle, outside repo)
- Read: working tree, `df -h`

- [ ] **Step 1: Confirm starting branch and clean-tool availability**

Run:
```bash
cd ~/Projects/brockian-mathematics
git rev-parse --abbrev-ref HEAD                 # expect: snapshot/brockian-dirty-2026-08-29
command -v gitleaks && command -v gh && command -v rg   # all three must resolve
```
Expected: current branch is `snapshot/brockian-dirty-2026-08-29`; `gitleaks`, `gh`, and `rg` paths print. If `gh` is missing, STOP and install it (`brew install gh`). If `rg` is missing, STOP (Step 3's secondary net silently no-ops without it).

> **Shell note:** the Bash tool runs **zsh**, not bash. `${PIPESTATUS[...]}` is empty in zsh and `$?` after a pipeline reflects the LAST command in the pipe (e.g. `tail`), not the tool you care about. Every exit-critical check below therefore captures the exit code **directly, without a pipe**. Do not "simplify" these by re-adding pipes.

- [ ] **Step 2: Disk headroom check (≥15 GB free)**

Run:
```bash
df -g ~ | awk 'NR==2 {print "free_GB="$4}'
```
Expected: `free_GB` ≥ 15. **Known-current condition (2026-09-11): this machine is ~10 GB free — below the floor — so this step WILL halt on first run.** Prune scratch caches per `~/.claude/.../memory/disk-cleanup-aug20.md` (Docker/Chrome/npm caches, hermes dumps) and re-run. Do NOT delete anything under `~/.orbstack`. Re-check until ≥15 GB. Do not proceed under the floor — the heavy push (Task 5) needs the headroom.

- [ ] **Step 3: Secrets scan over the ENTIRE working tree (tracked + untracked)**

Run (exit captured directly — no pipe):
```bash
gitleaks detect --no-git --redact --report-path /tmp/brockian-gitleaks.json
gl_exit=$?                                   # gitleaks: 0 = clean, 1 = leaks found
echo "gitleaks_exit=$gl_exit"
# Count findings from the report itself (gitleaks writes [] when clean):
gl_findings=$(python3 -c "import json;print(len(json.load(open('/tmp/brockian-gitleaks.json'))))" 2>/dev/null || echo "REPORT_UNREADABLE")
echo "gitleaks_findings=$gl_findings"
# Secondary pattern net (gitleaks can miss custom formats); count matches:
rg -n --no-heading -e 'sk-or-v1-' -e 'sk-proj-' -e 'sk-ant-' \
   -e 'SUPABASE_SERVICE_ROLE' -e 'B2_ACCOUNT_KEY' -e 'AKIA[0-9A-Z]{16}' \
   -e 'ghp_[0-9A-Za-z]{36}' -e 'xoxb-' \
   -g '!**/.git/**' . > /tmp/brockian-rg-secrets.txt
rg_hits=$(wc -l < /tmp/brockian-rg-secrets.txt | tr -d ' ')
echo "rg_secret_hits=$rg_hits"
```
Expected: `gitleaks_exit=0`, `gitleaks_findings=0`, `rg_secret_hits=0`.

- [ ] **Step 4: HARD GATE — evaluate scan results**

Inspect the three values from Step 3. If ANY of these is true —
`gl_exit` ≠ 0, OR `gl_findings` ≠ 0 (or `REPORT_UNREADABLE`), OR `rg_secret_hits` ≠ 0 —
then **STOP. Do not commit.** Read the offenders:
```bash
python3 -c "import json;[print(f['File'],f.get('StartLine'),f['RuleID']) for f in json.load(open('/tmp/brockian-gitleaks.json'))]" 2>/dev/null
cat /tmp/brockian-rg-secrets.txt
```
Surface the exact file+line to the human for removal/rotation and wait. Do not proceed to Task 2 until the human confirms the tree is clean. If all three values are the expected zeros: proceed.

- [ ] **Step 5: Create rollback safety net (tag + bundle)**

Run:
```bash
git tag -f pre-consolidation-2026-09-10 HEAD
git bundle create ~/brockian-pre-consolidation-2026-09-10.bundle --all
ls -lh ~/brockian-pre-consolidation-2026-09-10.bundle
git bundle verify ~/brockian-pre-consolidation-2026-09-10.bundle | tail -3
```
Expected: bundle file exists (non-zero size) and `git bundle verify` reports it is OK. This tag marks the exact pre-consolidation state for rollback.

> **Note:** `--all` bundles only *committed* refs. At this point the 24k-file working tree is still uncommitted, so it is **not** in this bundle. Task 2 Step 7 refreshes the bundle after everything is committed, so the full tree is captured offsite before the merge.

- [ ] **Step 6: Checkpoint (no commit yet)**

State to the human: disk free GB, secrets-scan result (CLEAN), bundle path + size. This is a human-review checkpoint before any history is written. Proceed on acknowledgement.

---

### Task 2: Commit the working tree in themed commits (U2)

**Files:**
- Modify (commit): all 24,488 changed paths on `snapshot/brockian-dirty-2026-08-29`

**Note:** "commit everything" is the user's explicit choice — scratch (`harvest_100/`, `mined_lemmas/`) becomes permanent history. Themed commits below make the eventual PR reviewable; they do not drop anything.

- [ ] **Step 1: Snapshot the pending change inventory (for the log)**

Run:
```bash
git status --porcelain | awk '{print $1}' | sort | uniq -c
git status --porcelain | wc -l          # record total
```
Expected: ~3,710 `M` + ~20,778 `??` ≈ 24,488 total. Record these numbers for the CONSOLIDATION-LOG (Task 6).

- [ ] **Step 2: Commit theme 1 — registry + attestations regen**

Run:
```bash
git add registry/theorems.json REGISTRY.md registry/attestations/
git commit --no-verify -m "registry: refresh to current attested state (PROVED ~12,373)

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```
Expected: commit succeeds. (If nothing staged because these are already committed on snapshot, that is fine — skip to next theme.)

- [ ] **Step 3: Commit theme 2 — new verified proofs**

Run:
```bash
git add aristotle/best_proofs/
git commit --no-verify -m "proofs: add newly harvested best_proofs (~47 new .lean)

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>" || echo "nothing to commit for this theme"
```
Expected: commit succeeds or "nothing to commit".

- [ ] **Step 4: Commit theme 3 — remaining tracked modifications**

Run:
```bash
git add -u
git commit --no-verify -m "audits/data: refresh modified tracked files (axle audits, aristotle json)

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>" || echo "nothing to commit for this theme"
```
Expected: commit succeeds or "nothing to commit". (`git add -u` stages only already-tracked modifications, not new untracked scratch.)

- [ ] **Step 5: Eyeball what remains, then commit theme 4 — pipeline scratch/byproduct (everything remaining)**

First inspect what `git add -A` is about to sweep, so nothing valuable is silently bucketed as "scratch":
```bash
git status --porcelain | sed 's/^/  /' | awk '{print $1}' | sort | uniq -c
git status --porcelain | grep -vE 'aristotle/harvest_100/|aristotle/mined_lemmas/' | head -40
```
Expected: the second command shows only genuine byproduct paths. If it surfaces untracked docs/specs/KG data that belong in a themed commit, `git add` + commit those first with an appropriate message. Then:
```bash
git add -A
git commit --no-verify -m "pipeline: commit harvest_100/ + mined_lemmas/ byproducts (full-tree preservation)

Per Phase-1 decision to commit everything. Future .gitignore cleanup tracked in CONSOLIDATION-LOG.

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>" || echo "nothing left to commit"
```
Expected: commit succeeds or "nothing left to commit".

- [ ] **Step 6: Verify tree is fully clean**

Run:
```bash
git status --porcelain | wc -l          # expect 0
```
Expected: `0`. If non-zero, stage and commit the remainder with `git add -A && git commit --no-verify`. The working tree MUST be empty before merging.

- [ ] **Step 7: Refresh the rollback bundle to capture the now-committed full tree**

Run:
```bash
git tag -f pre-consolidation-2026-09-10 HEAD
git bundle create ~/brockian-pre-consolidation-2026-09-10.bundle --all
git bundle verify ~/brockian-pre-consolidation-2026-09-10.bundle | tail -3
```
Expected: bundle re-created and verifies OK. Now the full committed working tree (all 24k paths) is captured offsite before any merge touches history.

---

### Task 3: Consolidation merge (U3)

**Files:**
- Create: branch `consolidate/2026-09-10` (from `origin/main`)
- Modify (merge + regen): conflicted files per policy; `registry/theorems.json`, `REGISTRY.md`

- [ ] **Step 1: Fetch origin and create the consolidation branch from the governance line**

Run:
```bash
git fetch origin
git checkout -b consolidate/2026-09-10 origin/main
git log --oneline -1                     # expect origin/main tip 59912b4cc (or newer)
```
Expected: on branch `consolidate/2026-09-10` at `origin/main`'s tip (carries the promotion gate + governance scripts).

- [ ] **Step 2: Merge snapshot's content (do not auto-resolve blindly)**

Run:
```bash
git merge --no-ff --no-commit snapshot/brockian-dirty-2026-08-29 || true
git status --porcelain | grep -E '^(UU|AA|DD|U|.U)' | sed 's/^/  /'
```
Expected: merge pauses (either clean-staged awaiting commit, or with conflicts listed). Conflicts are expected in files both lines touched: `.github/workflows/ci.yml`, `scripts/proof_assimilation.py`, `aristotle/select_best.py`, `tests/test_proof_assimilation.py`, and the registry files.

- [ ] **Step 3: Resolve conflicts by deterministic policy**

For GOVERNANCE files (keep origin/main's gate semantics) — but first surface any snapshot-side functional delta so a genuine improvement isn't silently dropped (spec U3):
```bash
for f in .github/workflows/ci.yml .github/pull_request_template.md \
         .github/workflows/full-corpus-audit.yml \
         scripts/proof_assimilation.py scripts/check_attestation_integrity.py \
         aristotle/select_best.py provenance/verdicts.yaml \
         tests/test_proof_assimilation.py; do
  [ -e "$f" ] || continue
  # Show what snapshot changed relative to the governance version:
  delta=$(git diff --stat origin/main..snapshot/brockian-dirty-2026-08-29 -- "$f")
  if [ -n "$delta" ]; then
    echo "SNAPSHOT DELTA on governance file $f:"; echo "$delta" | sed 's/^/    /'
    echo "  -> review: is this a real functional improvement to re-apply on top of origin's version? Log the decision in CONSOLIDATION-LOG."
  fi
  git checkout --ours -- "$f" 2>/dev/null && git add "$f" && echo "ours(origin): $f"
done
```
For any governance file that printed a non-trivial `SNAPSHOT DELTA`: after taking origin's version, manually re-apply the snapshot-side functional change on top (if it is a genuine improvement) and record what you re-applied (or deliberately dropped) in the CONSOLIDATION-LOG. Do not commit the merge (Step 5) until each such delta has an explicit logged decision.
For CONTENT files (keep snapshot's newer work) — resolve each remaining conflict toward snapshot:
```bash
git diff --name-only --diff-filter=U | while read f; do
  case "$f" in
    registry/*|Brockian/*|aristotle/best_proofs/*|docs/*|torus/*|visualizations/*|datasets/*|data/*)
      git checkout --theirs -- "$f" && git add "$f" && echo "theirs(snapshot): $f" ;;
    *)
      echo "MANUAL REVIEW NEEDED: $f" ;;   # anything unclassified → inspect, do not guess
  esac
done
```
Expected: every conflict is either resolved by policy or printed as "MANUAL REVIEW NEEDED". **For each MANUAL file: inspect both sides, resolve toward the honest/current version, and if it touches gate semantics, surface to the human.** Do not commit while any `MANUAL REVIEW NEEDED` remains.

- [ ] **Step 4: Confirm no conflict markers remain**

Run:
```bash
git diff --name-only --diff-filter=U          # expect empty
rg -n '^<<<<<<<|^>>>>>>>|^=======$' -g '!**/.git/**' . | head
```
Expected: no unmerged paths; no conflict markers anywhere.

- [ ] **Step 5: Commit the merge**

Run:
```bash
git commit --no-verify -m "merge: consolidate snapshot content into governance trunk

Governance files (gate/ci/assimilation) from origin/main; content/registry/proofs from
snapshot/brockian-dirty-2026-08-29 (superset of conveyor+codex). See CONSOLIDATION-LOG.md.

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```
Expected: merge commit created.

- [ ] **Step 6: Regenerate the registry mechanically (gate requires derive == committed)**

Run:
```bash
python3 scripts/gen_registry.py
git diff --stat registry/theorems.json REGISTRY.md
```
Expected: either no diff (already consistent) or a diff reflecting the mechanical regeneration. If there is a diff, commit it:
```bash
git add registry/theorems.json REGISTRY.md
git commit --no-verify -m "registry: mechanical regeneration post-merge (derive == committed)

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 4: Local gate dry-run — mirror CI exactly (U4)

**Files:**
- Read/run: the gate scripts on `consolidate/2026-09-10`
- Base SHA for change-detection = `origin/main`

- [ ] **Step 1: Compute the base SHA and confirm zero gated-Lean changes**

Run:
```bash
BASE=$(git rev-parse origin/main); echo "BASE=$BASE"
git diff --name-only --diff-filter=ACMR "$BASE" HEAD -- 'Brockian/*.lean' 'Brockian/**/*.lean' | tee /tmp/changed-lean.txt
echo "changed_lean_count=$(wc -l < /tmp/changed-lean.txt)"
```
Expected: `changed_lean_count=0` → the gate's Lean kernel legs are skipped (`has_lean=false`). If NON-zero, STOP: a `Brockian/**/*.lean` change would require content-hash-bound attestations; surface to human before continuing.

- [ ] **Step 2: Control-plane unit tests (verbatim CI list)**

Run:
```bash
python3 -m pip install --quiet pyyaml pytest
python3 -m pytest \
  tests/test_proof_assimilation.py tests/test_select_best.py tests/test_attest.py \
  tests/test_gen_registry.py tests/test_attestation_integrity.py \
  tests/test_audit_registry_consistency.py tests/test_no_theater_lint.py \
  tests/test_engine_register.py tests/test_engine_verify.py tests/test_ingest_discover.py \
  tests/test_conveyor.py tests/test_conveyor_paperclip.py tests/test_conveyor_notify.py \
  tests/test_export_obsidian.py -q
```
Expected: all pass. On failure, fix the underlying data/registry (never weaken the test) and re-run.

- [ ] **Step 3: Registry-derived-from-receipts check (gate's exact command)**

Run:
```bash
python3 scripts/gen_registry.py
git diff --exit-code registry/theorems.json REGISTRY.md
echo "derive_diff_exit=$?"
```
Expected: `derive_diff_exit=0` (registry equals its regeneration). If non-zero, commit the regeneration (as in Task 3 Step 6) and re-run.

- [ ] **Step 4: Attestation integrity + no-theater lint**

Run:
```bash
python3 scripts/check_attestation_integrity.py --strict --require-content-hash-for-changed "$BASE"
CLOSED=$(python3 -c "import yaml;print(' '.join(yaml.safe_load(open('provenance/verdicts.yaml')).get('closed_modules',[])))")
python3 scripts/no_theater_lint.py Brockian/*.lean --closed $CLOSED
```
Expected: both exit 0.

- [ ] **Step 5: Registry/firewall/manifest audits (gate's exact commands)**

Run:
```bash
python3 scripts/proof_assimilation.py --output /tmp/pa.json --review /tmp/pa.REVIEW.md
python3 scripts/audit_registry_consistency.py --strict --limit 20
python3 scripts/verify_firewall.py
python3 scripts/validate_manifests.py
```
Expected: all exit 0. Capture stdout of every step in this task into `/tmp/brockian-gate-dryrun.log` for the CONSOLIDATION-LOG.

- [ ] **Step 6: Green-light checkpoint**

Only when EVERY step above is green: report the all-green transcript to the human. This confirms the PR CI will pass. Proceed to push.

---

### Task 5: Push, PR, and merge through CI (U5)

**Files:**
- Push: `consolidate/2026-09-10` → `origin`
- Create: PR → `main`

- [ ] **Step 1: Final disk check before the heavy push**

Run:
```bash
df -g ~ | awk 'NR==2 {print "free_GB="$4}'
```
Expected: ≥15 GB. If tight, prune and re-check before pushing.

- [ ] **Step 2: Single push, monitoring disk**

Run (exit captured directly — no pipe, per the zsh shell note in Task 1):
```bash
git push -u origin consolidate/2026-09-10
push_exit=$?
echo "push_exit=$push_exit"
df -g ~ | awk 'NR==2 {print "free_GB_after="$4}'
```
Expected: `push_exit=0`. If the push fails (size/pack/disk), FALLBACK: push the branch history in stages using an intermediate ref (push up to the merge commit first, then the scratch commit), re-checking disk between pushes. Do not retry blindly in a loop.

- [ ] **Step 3: Open the PR using the repo template**

Run:
```bash
gh pr create --base main --head consolidate/2026-09-10 \
  --title "Consolidate verified corpus → main (PROVED ~12,373, KG v3, NS/Euler)" \
  --body "Consolidates snapshot (content superset of conveyor+codex) with origin/main governance line.
Registry regenerated mechanically; local promotion-gate dry-run green (see CONSOLIDATION-LOG.md).
Full working tree committed per Phase-1 decision. Rollback: tag pre-consolidation-2026-09-10 + bundle."
gh pr view --json url -q .url
```
Expected: PR URL prints.

- [ ] **Step 4: Wait for CI `promotion-gate` and report status**

Run:
```bash
gh pr checks --watch 2>&1 | tail -20
```
Expected: `promotion-gate` passes. If any check is red, fetch the failing log (`gh run view --log-failed`), fix on `consolidate/2026-09-10` (re-run relevant Task-4 step locally first), push a follow-up commit, and re-watch. The fix is always to make the work honest — never to weaken the gate.

- [ ] **Step 5: Merge the PR (no force-push to main)**

Run:
```bash
gh pr merge --merge --delete-branch=false 2>&1 | tail -5
```
Expected: PR merged into `main`. (Use `--merge`, not `--squash`, to preserve the themed/governance history; adjust only if repo convention differs.)

- [ ] **Step 6: Confirm CI green on main**

Run:
```bash
git fetch origin
gh run list --branch main --limit 1
```
Expected: latest `main` run is green.

---

### Task 6: Post-merge verification + CONSOLIDATION-LOG + release (U6)

**Files:**
- Create: `CONSOLIDATION-LOG.md` (repo root)
- Create: release tag `v2026.09.10-consolidation`
- Modify: `~/.claude/projects/-Users-acutis/memory/MEMORY.md` (+ a topic file)

- [ ] **Step 1: Verify origin/main is now current and honest**

Run:
```bash
git cat-file -p origin/main:registry/theorems.json | python3 -c "import sys,json;print('PROVED', json.load(sys.stdin)['summary']['PROVED'])"
git cat-file -p origin/main:REGISTRY.md | grep -m1 -i 'PROVED'
git ls-tree origin/main -- docs/superpowers/specs/2026-09-08-nse-verify-visualize-design.md docs/superpowers/specs/2026-09-06-knowledge-graph-v3-design.md
```
Expected: PROVED count matches the working-tree count (~12,373–12,374); REGISTRY.md PROVED line agrees; KG v3 + NS/Euler specs are present on `origin/main`.

- [ ] **Step 2: Confirm registry parity (acceptance test #2)**

Run:
```bash
git checkout consolidate/2026-09-10
python3 scripts/audit_registry_consistency.py --strict --limit 20 && echo "PARITY OK"
```
Expected: `PARITY OK`.

- [ ] **Step 3: Write CONSOLIDATION-LOG.md**

Create `CONSOLIDATION-LOG.md` documenting: PROVED before (origin/main pre-merge) → after; branches merged (snapshot superset of conveyor+codex) and the 5 governance commits preserved; the conflict-resolution policy applied and each MANUAL file's resolution; the disk + secrets-scan results; the local gate dry-run transcript summary; the release tag; the rollback bundle path; and a note that `harvest_100/` + `mined_lemmas/` scratch was committed intentionally with a **future `.gitignore` cleanup** offered as a deliberate follow-up.

- [ ] **Step 4: Commit the log and tag a release**

Run:
```bash
git add CONSOLIDATION-LOG.md
git commit --no-verify -m "docs: CONSOLIDATION-LOG for 2026-09-10 GitHub sync

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
git push origin consolidate/2026-09-10
# After this lands on main via a trivial fast-follow PR or direct include, tag main:
git fetch origin && git tag v2026.09.10-consolidation origin/main && git push origin v2026.09.10-consolidation
```
Expected: log committed; release tag pushed. (If branch protection blocks tagging from a non-merged commit, tag the merge commit on `main` after Step 6-merge.)

- [ ] **Step 5: Update memory**

Add a topic file `~/.claude/projects/-Users-acutis/memory/brockian-github-consolidation.md` (type: project) recording: origin/main is now current as of 2026-09-10, canonical trunk = `main` gated by `promotion-gate`, snapshot was the pre-consolidation superset, rollback tag/bundle exist, Phases 2–3 (front door, unified site) still pending. Add a one-line pointer under the appropriate MEMORY.md section, linking `[[brockian-serious-math-program]]`.

- [ ] **Step 6: Final report to human**

Report: origin/main PROVED before→after, PR URL, CI status, release tag, and the pending Phase 2/3 work. Phase 1 acceptance criteria (spec §Testing/acceptance) all satisfied.

---

## Acceptance (Phase 1 complete when ALL hold)

1. `origin/main` CI `promotion-gate` green on the merge commit.
2. `origin/main` REGISTRY.md and `registry/theorems.json` agree on PROVED count.
3. KG v3 graph, NS/Euler specs, and new `best_proofs` present on `origin/main`.
4. No secret in pushed history (Task 1 scan clean).
5. `pre-consolidation-2026-09-10` tag + `~/brockian-pre-consolidation-2026-09-10.bundle` exist.
6. `CONSOLIDATION-LOG.md` on `main`; release tag `v2026.09.10-consolidation` pushed.
