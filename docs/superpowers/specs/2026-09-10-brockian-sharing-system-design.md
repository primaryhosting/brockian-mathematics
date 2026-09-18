# Brockian Mathematics — Best-Possible Sharing System (Design)

> Date: 2026-09-10
> Owner: Christopher Brock
> Status: Phase 1 detailed and approved; Phases 2–3 sketched (each gets its own spec later)
> Repo: `primaryhosting/brockian-mathematics`

## Problem

The mathematics is thriving but the **sharing** is fragmented. The public GitHub
`origin/main` is stale as of 2026-08-27 (`59912b4cc`), while the freshest verified
work is trapped across divergent local branches and a large uncommitted working tree.
Anyone visiting the repo — mathematicians, formal-methods collaborators, funders/press,
or the internal agent fleet — sees a months-old snapshot that undersells the program.

### Verified current state (2026-09-10 audit)

- **Registry (working tree):** `PROVED 12373`, `DEFINITION 651`, `CONJECTURE 40`,
  `CONDITIONAL 33`, `DISCHARGED 7` (13,104 declarations total). `registry/theorems.json`
  is the single source of truth; `REGISTRY.md` is its rendered view.
- **Branch topology:** all feature branches fork from `847abdb46` (local `main` tip).
  - `snapshot/brockian-dirty-2026-08-29` = base + 51 feature commits, and is a **strict
    superset** of both `conveyor/2026-08-18` (+43) and `codex/proof-assimilation` (+24).
    Verified via `git merge-base --is-ancestor` (both return YES).
  - `origin/main` = base + **5 governance commits** that the local lineage lacks:
    proof assimilation + candidate fallback (`2f040c38a`), hash-bound GitHub promotion
    gate (`841fb4bc1`), fail-closed ambiguous-axiom attestation (`f0b8959df`), and two
    PR merges (#9, #10).
- **Uncommitted working tree:** 24,488 changed paths — 3,710 modified + 20,778 untracked.
  The untracked mass is overwhelmingly **pipeline scratch/byproduct**
  (`aristotle/harvest_100/` ≈ 4,008 dirs, `aristotle/mined_lemmas/*`). The genuinely
  valuable-and-uncommitted deltas are: registry+attestation regen (12,373 PROVED),
  ~47 new `aristotle/best_proofs/*.lean`, plus KG v3 + NS/Euler specs (already committed
  on `snapshot`).
- **The gated source is unchanged:** `git status` reports **zero** working-tree
  modifications under `Brockian/**/*.lean`. The promotion gate only inspects
  `Brockian/**/*.lean`, so consolidation will **not** trip the source-bound
  attestation-integrity check.

### The promotion gate (existing machinery — the credibility spine)

`.github/workflows/ci.yml` on `origin/main` defines a `promotion-gate` job that runs on
push to `main` and on PRs:

1. Compute the changed `Brockian/**/*.lean` set vs the base SHA.
2. Control-plane unit tests: `test_proof_assimilation`, `test_select_best`, `test_attest`,
   `test_gen_registry`, `test_attestation_integrity`, `test_audit_registry_consistency`,
   `test_no_theater_lint`, `test_engine_register`, `test_engine_verify`,
   `test_ingest_discover`, `test_conveyor*`, `test_export_obsidian`.
3. `scripts/proof_assimilation.py` — proof comparison + steering report.
4. `scripts/check_attestation_integrity.py --strict --require-content-hash-for-changed <base>`
   — every changed Lean file must carry a content-hash-bound attestation.
5. `scripts/no_theater_lint.py` over closed modules from `provenance/verdicts.yaml`.
6. `scripts/verify_firewall.py` — dependency-firewall check.
7. `scripts/validate_manifests.py` — manifest validation.
8. `scripts/audit_registry_consistency.py --strict --limit 20` — REGISTRY.md ↔
   `registry/theorems.json` consistency.
9. `scripts/gen_registry.py` derive-and-diff — the registry must equal its mechanical
   regeneration (no hand edits).

**Design principle:** the sharing system's credibility *is* this gate. Consolidation must
land **through** the gate via a PR — never by force-pushing around it.

## Audiences (all four)

1. **Research mathematicians** — need to see exactly what is PROVED vs conjectured, the
   Lean source, the AXLE attestations, and reproducibility.
2. **Formal-methods collaborators** (Galois, AXLE, Mathlib, Aristotle) — care about the
   verification pipeline, PR candidates, machine-checkable claims.
3. **Public / funders / press** — need the story, the visuals (RiemannLab labs,
   number-line), and credibility signals; discover via the web, not GitHub.
4. **Internal (Chris + agent fleet)** — the repo as honest operational source of truth.

## Goals / Non-goals

**Goals (Phase 1).** Get `origin/main` current and honest (12,373 PROVED, KG v3,
NS/Euler specs, ~47 new proofs, refreshed attestations) via a gated promotion PR;
preserve the full working tree ("commit everything"); preserve origin's 5 governance
commits; lose nothing (safety tag + bundle); commit no secrets.

**Non-goals (Phase 1).** No README/website redesign (Phase 2/3). No refactor of the
verification pipeline. No `.gitignore` removal of scratch (user chose to commit
everything; a future cleanup is offered but not performed).

---

## Phase 1 — Consolidate & Sync GitHub (detailed, approved)

Strategy **A: Gated promotion PR**. Scratch handling: **commit everything** (full working
tree preserved as-is), organized into themed commits for review.

### Units of work

Each unit has one purpose, a defined interface (inputs → outputs), and is independently
checkable.

#### U1. Pre-flight safety gate
- **Purpose:** guarantee the operation is reversible and secret-free before any commit.
- **Inputs:** current working tree; `df -h ~`.
- **Actions:**
  - Disk headroom check. If free space is below a 15 GB floor, prune known scratch caches
    per the disk-cleanup runbook before proceeding; re-check.
  - **Secrets scan** over tracked + untracked files (`gitleaks detect --no-git` over the
    working tree, plus a pattern grep for `sk-`, `sk-or-v1`, `sk-proj-`, AWS keys,
    `SUPABASE_SERVICE_ROLE`, `B2_ACCOUNT_KEY`, bearer tokens). **On any hit: STOP, do not
    commit, surface the file+line to the human** for rotation/removal. This is a hard gate
    even though the user chose "commit everything."
  - Create safety net: `git tag pre-consolidation-2026-09-10` on `snapshot`'s current tip,
    and `git bundle create ~/brockian-pre-consolidation-2026-09-10.bundle --all`.
- **Output:** GO/NO-GO; safety tag + bundle on disk.
- **Done when:** scan clean (or human-cleared), bundle written, ≥15 GB free.

#### U2. Commit the working tree (themed)
- **Purpose:** turn the 24,488-path dirty tree into a reviewable committed history on
  `snapshot`, committing everything.
- **Interface:** working tree → N themed commits on `snapshot/brockian-dirty-2026-08-29`.
- **Actions:** stage and commit in themed groups, in this order:
  1. `registry/` + `registry/attestations/` regen (the 12,373-PROVED state).
  2. New `aristotle/best_proofs/*.lean` (the ~47 new verified proofs).
  3. Remaining modified tracked files (`aristotle/*.json` audits, etc.).
  4. Pipeline scratch (`aristotle/harvest_100/`, `aristotle/mined_lemmas/`) — one bulk
     commit, explicitly labeled as byproduct.
- **Output:** clean `git status`; every path committed.
- **Done when:** `git status --porcelain` is empty.

#### U3. Consolidation merge
- **Purpose:** unify the feature line with the governance line.
- **Interface:** (`origin/main`, `snapshot`) → new branch `consolidate/2026-09-10`.
- **Actions:**
  - `git fetch origin`; `git checkout -b consolidate/2026-09-10 origin/main`.
  - `git merge snapshot/brockian-dirty-2026-08-29`.
  - **Conflict-resolution policy (deterministic):**
    - `.github/**`, `scripts/proof_assimilation.py`, `scripts/check_attestation_integrity.py`,
      `aristotle/select_best.py`, `provenance/verdicts.yaml`, and any governance/gate file
      → **take `origin/main`'s version**, then re-apply any snapshot-side *functional*
      delta on top (documented in the CONSOLIDATION-LOG).
    - `registry/**`, `Brockian/**`, `aristotle/best_proofs/**`, `docs/**`, `torus/**`,
      `visualizations/**`, KG graph data → **take `snapshot`'s version** (content wins).
  - Regenerate the registry mechanically after the merge (`python3 scripts/gen_registry.py`
    or the repo's canonical generator) so `registry/theorems.json` + `REGISTRY.md` are
    internally consistent and not a hand-merged artifact.
- **Output:** `consolidate/2026-09-10` with no conflict markers; regenerated registry.
- **Done when:** merge committed; `grep -rl '^<<<<<<<' .` returns nothing.

#### U4. Local gate dry-run (mirror CI exactly)
- **Purpose:** prove the PR will pass before pushing.
- **Interface:** `consolidate/2026-09-10` → PASS/FAIL report.
- **Actions:** run **every** CI step locally against the base = `origin/main` SHA. Derive
  the exact command list by parsing the **merged** `.github/workflows/ci.yml` (not a
  hand-copied list) so U4 cannot drift from CI. As of the reviewed gate that is:
  - the control-plane pytest set from `ci.yml` (verbatim list),
  - `python3 scripts/proof_assimilation.py --output /tmp/pa.json --review /tmp/pa.REVIEW.md`,
  - `python3 scripts/check_attestation_integrity.py --strict --require-content-hash-for-changed <origin/main SHA>`,
  - `python3 scripts/no_theater_lint.py Brockian/*.lean --closed <closed_modules>`,
  - `python3 scripts/verify_firewall.py`,
  - `python3 scripts/validate_manifests.py`,
  - `python3 scripts/audit_registry_consistency.py --strict --limit 20`,
  - `python3 scripts/gen_registry.py` derive-and-diff (registry equals its regeneration).
  - (The Lean kernel-build leg is skipped because `Brockian/**/*.lean` is unchanged →
    the gate's `has_lean=false` branch; U1 already verified zero changes there.)
- **Output:** all-green transcript captured into the CONSOLIDATION-LOG. On any failure,
  fix within the merge (regenerate/attach missing attestation, correct registry) and re-run.
- **Done when:** every gate step passes locally.

#### U5. Push + PR + merge
- **Purpose:** land the consolidation on `origin/main` through CI.
- **Actions:**
  - Check `df` again; push `consolidate/2026-09-10` in a **single** push while monitoring
    disk (memory: big pushes have spiked disk to 100%). If the push is rejected for size or
    disk fails, fall back to pushing in stages (governance-merge commit first, scratch
    commit last).
  - Open a PR → `main` using the repo's `pull_request_template.md`.
  - CI `promotion-gate` runs. Fix any red step, push follow-up commits, repeat.
  - Merge the PR (squash or merge-commit per repo convention — do **not** force-push main).
- **Output:** `origin/main` advanced to the consolidated state.
- **Done when:** PR merged, CI green on `main`.

#### U6. Post-merge verification + record
- **Purpose:** confirm the public trunk is now current and honest; make the change legible.
- **Actions:**
  - Verify `git cat-file -p origin/main:registry/theorems.json` shows `PROVED 12373`
    (or the then-current count) and `REGISTRY.md` matches (`audit_registry_consistency`).
  - Confirm KG v3 graph + NS/Euler specs + new proofs are present on `origin/main`.
  - Tag a release (e.g. `v2026.09.10-consolidation`).
  - Write `CONSOLIDATION-LOG.md` at repo root: branches merged, conflict resolutions,
    gate transcript, PROVED before/after, release tag, bundle location.
  - Update `~/.claude/.../memory/MEMORY.md` pointer.
- **Done when:** parity verified, release tagged, log committed, memory updated.

### Data flow

```
working tree (dirty)
  └─U1 safety→ tag + bundle + secrets-clean
  └─U2 commit→ snapshot (all paths committed, themed)
origin/main (governance) ─┐
snapshot (content) ───────┴─U3 merge→ consolidate/2026-09-10 → regen registry
  └─U4 local gate (mirror CI) → PASS
  └─U5 push → PR → promotion-gate CI → merge → origin/main
  └─U6 verify + tag + CONSOLIDATION-LOG
```

### Error handling

- **Secrets found (U1):** hard stop; surface to human; do not proceed until cleared.
- **Disk pressure (U1/U5):** prune scratch caches, re-check; stage the push if needed.
- **Merge conflicts (U3):** resolved by the deterministic policy above; any ambiguity is
  logged and, if it touches a governance file's semantics, surfaced to the human.
- **Gate failure (U4/U5):** treat as authoritative — the fix is to make the work honest
  (attach the missing attestation, regenerate the registry), never to weaken the gate.
- **Registry inconsistency:** always regenerate mechanically (U3), never hand-edit.

### Testing / acceptance

Phase 1 is accepted when **all** hold:
1. `origin/main` CI `promotion-gate` is green on the merge commit.
2. `origin/main:registry/theorems.json` and `REGISTRY.md` agree on the PROVED count
   (12,373 or then-current) — `test_audit_registry_consistency` passes.
3. KG v3 graph, NS/Euler specs, and the new `best_proofs` are present on `origin/main`.
4. No secret appears in the pushed history (scan clean).
5. `pre-consolidation-2026-09-10` tag + bundle exist (rollback path intact).
6. `CONSOLIDATION-LOG.md` documents the operation.

### Risks & mitigations

| Risk | Mitigation |
|------|------------|
| Big push spikes disk to 100% | Prune first; single push; stage fallback; monitor `df` during push |
| Conflicts in `ci.yml`/`proof_assimilation.py`/`select_best.py` (both lines touched them) | Deterministic policy: governance files ← origin, re-apply snapshot functional deltas, log each |
| Secret in the 20k committed files | U1 secrets scan is a hard gate |
| Heavier repo from committing scratch | Honored per user choice; future `.gitignore` cleanup offered in CONSOLIDATION-LOG, not performed |
| Hand-merged registry drifts from attestations | Always regenerate mechanically post-merge |

---

## Phase 2 — GitHub front door (sketch; own spec later)

Redesign the first thing every audience sees on GitHub:
- A layered `README` (30-second story → verification discipline → how to reproduce →
  domain map), with the **promotion gate rendered as a visible badge** (credibility signal).
- Auto-generated `REGISTRY.md` upgraded to **per-domain rollups** (Brockian, Erdős, SAIR,
  CS/Physics frontier) with PROVED/CONDITIONAL/CONJECTURE counts and links to source +
  attestation for each headline theorem.
- A short "for collaborators" page surfacing Mathlib PR candidates and the pipeline.

## Phase 3 — Unified public findings site (sketch; own spec later)

One public destination that merges **Lean proofs + RiemannLab labs** (torus.riemannlab.com,
number-line) so funders/press get story + visuals + a live, registry-backed proof count in
one place, with the repo as the data source. Reuses the KG v3 graph as an interactive map.

---

## Open questions (Phase 1)

None blocking.
- The canonical registry generator is `scripts/gen_registry.py` (confirmed present and the
  entrypoint CI invokes). The conveyor-path alternative is dropped unless U3 finds a
  difference.
- The PROVED count is **read-at-time**, not hard-coded: the working tree currently shows
  ~12,373–12,374 and may advance before the merge lands. Acceptance test #2 checks
  REGISTRY.md ↔ JSON *parity*, not a fixed number.
