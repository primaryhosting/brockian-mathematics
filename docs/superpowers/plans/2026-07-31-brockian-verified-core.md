# Brockian Verified Core — Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build one public, CI-verified `brockian-mathematics` Lean repo whose keeper-proofs compile under `lake build`, pass `#print axioms`, are independently AXLE-verified, and are surfaced through a machine-generated `registry/theorems.json` that the paper and website will consume.

**Architecture:** A one-time ingest pulls ledger-ADMITTED Lean declarations from ~7 scattered locations into seven consolidated `Brockian/*.lean` modules on one latest-stable toolchain. Porting races three levers per target (Aristotle generate / hand-port / AXLE `repair_proofs`); a declaration is PROVED only on triple verification (local `lake build` + local `#print axioms` clean + independent AXLE `verified`). Two Python scripts (`gen_registry.py`, `no_theater_lint.py`) and a `provenance/verdicts.yaml` map turn the compiled environment into the registry and enforce the register discipline in CI.

**Tech Stack:** Lean 4 + Mathlib (latest stable w/ cache), Lake, Python 3 (registry + lint + AXLE HTTP client), Aristotle CLI (`aristotlelib`), AXLE HTTP API (`axle.axiommath.ai/api/v1`), GitHub Actions.

**Spec:** `docs/superpowers/specs/2026-07-30-brockian-verified-core-design.md`

---

## File structure

| File | Responsibility |
|------|----------------|
| `lean-toolchain`, `lakefile.toml` | pin latest-stable Lean + matching Mathlib (cache-backed) |
| `Brockian/{Core,Admissibility,TransitionKernel,Geometry,GoldbachComb,Sieve,SpectralGate1}.lean` | the seven consolidated theme modules |
| `Brockian.lean` | root import |
| `provenance/verdicts.yaml` | hand-authored run-level + per-decl verdicts/provenance/closed-modules |
| `scripts/axle_client.py` | thin AXLE HTTP client (`check`/`verify_proof`) |
| `scripts/gen_registry.py` | compiled-env + AXLE + verdicts.yaml → `registry/theorems.json` + `REGISTRY.md` + `EXCLUDED.md` |
| `scripts/no_theater_lint.py` | grep known failure signatures → flags |
| `scripts/ingest_discover.py` | discover/dedup `.lean` sources → `_ingest/manifest.json` |
| `.github/workflows/ci.yml` | cache get → lake build → axiom check → AXLE verify → registry gen → gates |
| `EXCLUDED.md`, `PORT-QUEUE.md`, `REGISTRY.md` | generated audit artifacts |

---

## Chunk 1: Repo foundation & toolchain

**Outcome:** repo builds an empty-but-real `Brockian` lib on a cache-backed latest-stable toolchain; secret scan clean; CI skeleton green.

### Task 1.1: Choose toolchain + fix the pin

**Files:** Modify `lean-toolchain`, `lakefile.toml`

- [ ] **Step 1:** Determine the latest Mathlib stable tag with a prebuilt cache. Run:
  `git ls-remote --tags https://github.com/leanprover-community/mathlib4 'v4.*.0' | tail -8`
  then pick the newest `vX.Y.0` and read its `lean-toolchain` from
  `https://raw.githubusercontent.com/leanprover-community/mathlib4/<tag>/lean-toolchain`.
- [ ] **Step 2:** Set `lean-toolchain` to that exact `leanprover/lean4:vX.Y.Z`.
- [ ] **Step 3:** Rewrite `lakefile.toml` to require mathlib at the same tag; keep `name="brockian"`, `autoImplicit=false`, roots `["Brockian"]`, glob submodules `Brockian`.
- [ ] **Step 4:** `lake update` then `lake exe cache get` (Expected: downloads Mathlib oleans, minutes not hours).
- [ ] **Step 5:** Create a trivial `Brockian/Sanity.lean` (`theorem brockian_sanity : 1 + 1 = 2 := by decide`) + `Brockian.lean` importing it; `lake build` (Expected: PASS).
- [ ] **Step 6:** Commit `chore: pin latest-stable toolchain + mathlib cache; sanity build green`.

### Task 1.2: Pre-publish secret scan

**Files:** Create `scripts/secret_scan.sh`

- [ ] **Step 1:** Write `secret_scan.sh` grepping full history (`git log -p`) + working tree for key patterns (`sk-`, `sb_secret`, `AXLE_API_KEY=`, `ARISTOTLE_API_KEY=`, JWT `eyJ`, B2/restic patterns).
- [ ] **Step 2:** Run it. Expected: 0 hits (repo is math-only). If any hit → STOP, surface to human.
- [ ] **Step 3:** Commit `chore: add pre-publish secret scan (clean)`.

### Task 1.3: CI skeleton

**Files:** Create `.github/workflows/ci.yml`

- [ ] **Step 1:** Workflow: on push/PR → install elan, `lake exe cache get`, `lake build`. (Registry/axiom/AXLE gates added in later chunks.)
- [ ] **Step 2:** Commit; push branch; confirm Actions run is green.

---

## Chunk 2: Engine wiring (AXLE + Aristotle)

**Outcome:** a tested AXLE client that verifies real Lean cloud-side; Aristotle CLI confirmed usable.

### Task 2.1: AXLE HTTP client (TDD)

**Files:** Create `scripts/axle_client.py`, `tests/test_axle_client.py`

- [ ] **Step 1 (failing test):** `test_check_true_theorem` — `axle_client.check("import Mathlib\ntheorem t: 1+1=2 := by decide", env="lean-4.28.0")` returns `{verified: True, ...}`. (Live call; requires `AXLE_API_KEY`.)
- [ ] **Step 2:** Run → FAIL (module missing).
- [ ] **Step 3:** Implement `check(content, env)` and `verify_proof(candidate, statements, env)` → `POST https://axle.axiommath.ai/api/v1/{check,verify_proof}`, `Authorization: Bearer $AXLE_API_KEY`, parse verdict. Discover exact response schema from the first live response; normalize to `{verified: bool, raw: <json>, environment: env}`.
- [ ] **Step 4:** Run → PASS.
- [ ] **Step 5 (negative test):** `test_check_false_theorem` — a `sorry`-laden or false statement returns `verified: False`. Run → PASS.
- [ ] **Step 6:** Commit `feat: AXLE HTTP verification client + live tests`.

### Task 2.2: Confirm Aristotle + resolve environment

**Files:** Create `docs/engines.md`

- [ ] **Step 1:** `aristotle list` (Expected: past projects; confirms key works). Record.
- [ ] **Step 2:** Confirm the AXLE `environment` string that matches our chosen toolchain (from 2.1 live calls; may be baseline `lean-4.28.0` if latest not offered — record which, per spec §9).
- [ ] **Step 3:** Write `docs/engines.md`: how the plan invokes each engine, the resolved AXLE environment, the both-in-parallel race protocol. Commit.

---

## Chunk 3: Ingest & triage

**Outcome:** every `.lean` source discovered/deduped; `verdicts.yaml` authored for the must-port keepers; `EXCLUDED.md` generation working.

### Task 3.1: Discovery + dedup (TDD)

**Files:** Create `scripts/ingest_discover.py`, `tests/test_ingest_discover.py`

- [ ] **Step 1 (failing test):** on a fixture dir with 2 identical + 1 distinct `.lean`, `discover([dir])` returns 2 unique entries keyed by md5, each with path+size+md5.
- [ ] **Step 2:** Run → FAIL. **Step 3:** Implement. **Step 4:** Run → PASS.
- [ ] **Step 5:** Run for real over the 7 locations (spec §0); write `_ingest/manifest.json` (git-ignored). Record unique-file count in commit msg.
- [ ] **Step 6:** Commit `feat: corpus discovery + dedup manifest`.

### Task 3.2: Author `provenance/verdicts.yaml` for the must-port set

**Files:** Create `provenance/verdicts.yaml`, `provenance/SCHEMA.md`

- [ ] **Step 1:** Define YAML schema (run-level defaults + per-decl overrides + `closed_modules`) in `SCHEMA.md`, mirroring spec §3.2/§5.
- [ ] **Step 2:** Author run-level + override entries for the §8 must-port keepers, each `exclude` citing a ledger line: q−ν law (runs 74/49), `golden_unique_to_five` (73), λ₂(C₅) (88), Aut(C₅)≅D₅ + pentagon geometry (54/70/16), Dirichlet-on-rays (97), constellation/transition + twin exclusion (7/31/117), GC-1..3 (intake 18), silver eigensystem (intake 18). Set `closed_modules: [Core, Admissibility, TransitionKernel]`.
- [ ] **Step 3:** Commit `feat: verdicts.yaml for must-port keeper set (+ schema)`.

---

## Chunk 4: Module consolidation & porting (the swarm work)

**Outcome:** each of the seven modules builds green with its keepers; theater excluded; port-pending recorded.

> Execution: one subagent per module, in parallel where independent. Each subagent follows the **both-in-parallel race** (spec §3.4) per target and the **triple-verification** gate (spec §2A). Order: `Core` first (others import it), then the rest in parallel, `SpectralGate1` last.

### Task 4.1..4.7 (one per module) — same shape

For each module `M` in `Core, Admissibility, TransitionKernel, Geometry, GoldbachComb, Sieve, SpectralGate1`:

- [ ] **Step 1:** Assemble candidate declarations for `M` from `_ingest/manifest.json` filtered by `verdicts.yaml` (admit only).
- [ ] **Step 2:** Consolidate duplicates (keep canonical anchor per spec §3.3); write `Brockian/M.lean`.
- [ ] **Step 3:** `lake build Brockian.M`. For each failing decl, race Aristotle / hand-port / AXLE `repair_proofs` (spec §3.4); take first that builds.
- [ ] **Step 4:** Statement-fidelity audit each ported decl vs its ledger-admitted statement (RETURN on drift). Pin residual `exact?`.
- [ ] **Step 5:** `#print axioms` each PROVED-intended decl → must be ⊆ {propext, Classical.choice, Quot.sound}, no native_decide. Demote violators to COMPUTATION.
- [ ] **Step 6:** AXLE-verify each PROVED-intended decl (`scripts/axle_client.py`); record verdict+env.
- [ ] **Step 7:** Any keeper that no lever closes → add to `PORT-QUEUE.md` with the blocking error; if it's a §8 must-port item, flag release-blocking.
- [ ] **Step 8:** `lake build` green for `M`; commit `feat(M): consolidated + triple-verified module`.

### Task 4.8: Root import + full build

- [ ] **Step 1:** `Brockian.lean` imports all seven; delete `Brockian/Sanity.lean`.
- [ ] **Step 2:** move old `catalog/` → `Archive/catalog/` (excluded from globs); leave `paper/` untouched.
- [ ] **Step 3:** `lake build` (whole lib) green. Commit.

---

## Chunk 5: Registry generator + no-theater lint

**Outcome:** `registry/theorems.json`, `REGISTRY.md`, `EXCLUDED.md` generated; lint enforced.

### Task 5.1: Register-derivation core (TDD)

**Files:** Create `scripts/gen_registry.py`, `tests/test_gen_registry.py`

- [ ] **Step 1 (failing test):** `derive_register(axioms, flags, axle_verdict, rung)` → PROVED only when axioms⊆allowed ∧ no native_decide/sorry/exact ∧ axle_verdict=="verified"; COMPUTATION when native_decide; CONDITIONAL when rung set; CONJECTURE for defs. Table-driven cases.
- [ ] **Step 2:** Run → FAIL. **Step 3:** Implement `derive_register`. **Step 4:** Run → PASS.
- [ ] **Step 5:** Commit `feat: register derivation (triple-verification rule)`.

### Task 5.2: Declaration extraction + merge

- [ ] **Step 1:** Extract all `Brockian.*` decls (name/kind/statement/module/source) via a Lean metaprogram probe or `lake env lean` `#print axioms` parse (spec §6.2).
- [ ] **Step 2:** Merge build facts + AXLE verdicts + `verdicts.yaml` (override→run-default); error if a compiled PROVED/CONDITIONAL decl resolves to no provenance.
- [ ] **Step 3:** Emit `registry/theorems.json` (schema per spec §5), `REGISTRY.md`, `EXCLUDED.md` (from verdicts excludes).
- [ ] **Step 4:** Reverse check: every verdicts `exclude` ↔ an `EXCLUDED.md` row. Round-trip: every PROVED entry ↔ a real compiled decl.
- [ ] **Step 5:** Commit `feat: registry generation + audit artifacts`.

### Task 5.3: No-theater lint (TDD)

**Files:** Create `scripts/no_theater_lint.py`, `tests/test_no_theater_lint.py`

- [ ] **Step 1 (failing test):** fixtures flag `:= 0` "self-adjoint", `% (2*π)`, Nat `^(1/2)`, `True`-typed Prop field, `sorry`, `admit`; clean file → 0 flags.
- [ ] **Step 2:** Run → FAIL. **Step 3:** Implement. **Step 4:** Run → PASS.
- [ ] **Step 5:** Run over `Brockian/`; blocking on `sorry`/`admit` in `closed_modules` only. Commit.

---

## Chunk 6: CI gates + acceptance + publish

**Outcome:** CI enforces all gates; acceptance criteria met; repo public.

### Task 6.1: Wire full CI gates

**Files:** Modify `.github/workflows/ci.yml`

- [ ] **Step 1:** After `lake build`: run `gen_registry.py`, fail if any PROVED decl violates its gate (axioms/flags/AXLE) or lacks provenance; run `no_theater_lint.py` (block per closed-modules); assert must-port set present per spec §8; commit regenerated `registry/`+`REGISTRY.md` on main.
- [ ] **Step 2:** Record `lake build` log + resolved mathlib hash + AXLE env/verdicts as CI artifacts.
- [ ] **Step 3:** Push; confirm green. Commit.

### Task 6.2: README + acceptance sweep

- [ ] **Step 1:** Update `README.md`: honest framing, register legend, how to reproduce (`lake exe cache get && lake build`), link registry + EXCLUDED + PORT-QUEUE.
- [ ] **Step 2:** Walk spec §8 acceptance checklist; check every box or record the honest gap.
- [ ] **Step 3:** Commit `docs: README + acceptance sweep`.

### Task 6.3: Make public (gated)

- [ ] **Step 1:** Re-run `scripts/secret_scan.sh` → must be clean.
- [ ] **Step 2:** `gh repo edit primaryhosting/brockian-mathematics --visibility public` (after confirming secret scan clean).
- [ ] **Step 3:** Verify public URL loads; final commit `chore: publish verified core`.

---

## Notes for the executor

- **Never fake a green build** (spec §2A): no `maxHeartbeats` inflation, no added axioms, no `native_decide` smuggled into PROVED. Port-pending is the honest outcome; PORT-QUEUE.md records it.
- **Never trust an engine's self-report** (ledger run 4 smuggled `harmonicSorry`): triple gates run on every return.
- **Surgical commits**, explicit paths (per user standing preference); this is a clean repo so `git add <path>` per task.
- **Long-running:** Mathlib cache build + Aristotle async submits can take minutes–hours; Chunk 4 is the swarm-parallelizable bulk.
