# Unified Proof Engine — Design

**Date:** 2026-08-20
**Status:** Draft (approved for spec-review loop)
**Owner:** Chris Brock
**Scope:** Consolidate three overlapping proof engines into one shared machinery while
keeping two separate registers.

---

## 1. Problem

The repository grew three engines that do adjacent work with duplicated machinery:

1. **Aristotle conveyor** (`aristotle/`, live via `ai.brockian.conveyor`, every 15 min).
   Harvests Aristotle proofs, verifies them through AXLE, and catalogues them into
   `registry/domains.json`. Stages: `harvest_proofs → harvest_all → select_best →
   axle_verify → axle_axiom_audit → catalogue_domains → … → auto_pr → observatory`.

2. **Registry toolkit** (`scripts/`, manual bulk + live regen). Attests the curated
   Brockian Lean library: `Brockian/*.lean → attest.py (AXLE) → registry/attestations/*.json
   (854 files) → gen_registry.py → registry/theorems.json → export_public_registry.py →
   torus/public/verified-registry.json`.

3. **`pipeline/`** (dormant since 2026-08-03, ~1,700 lines). A domain-agnostic
   problem-card triage and bookkeeping layer (Erdős, SAIR, multi-domain). It models
   problems as JSON cards, derives a per-card register, and delegates verification —
   it never calls AXLE itself. Wired into no scheduler.

The engines are not in conflict; the problem is **duplication and drift**:

- **AXLE compile + axiom-audit logic exists at least twice** — the conveyor's
  `axle_verify.py` + `axle_axiom_audit.py` (per-proof, `lean-4.32.2`) and the registry's
  `attest.py` (per-module, `lean-4.32.0`). The two paths disagree on the Lean
  environment, and `lean-4.32.0` is now deprecated server-side.
- **The PROVED gate is copy-pasted in ≥3 files** — `gen_registry.derive_register`
  (`scripts/gen_registry.py:44`), `audit_registry_consistency.find_register_invariants`
  (`scripts/audit_registry_consistency.py:301`), and `verify_firewall.py` (#35). The
  `ALLOWED_AXIOMS` set is textually duplicated with "keep in sync" comments.
- **`normalize()` / `content_hash()` is redefined in ~6 files** (`axle_verify.py`,
  `axle_axiom_audit.py`, `cross_check.py`, `catalogue_domains.py`, `auto_pr.py`,
  `attest.py`) — a single formatting change must be made in six places or hashes
  silently stop matching.
- **`pipeline/`'s good idea — a domain-agnostic intake/triage front door — is stranded**
  because its verify step was never wired to AXLE.

The goal is a single, legible engine: one place that verifies, one place that decides
a register, one place that enforces honesty, one Lean environment — without merging the
two corpora, whose separation is a deliberate honesty guarantee.

## 2. Decisions (settled during brainstorming)

- **One machinery, two registers.** `registry/theorems.json` (authored Brockian
  library) and `registry/domains.json` (Aristotle harvest) stay **separate registers**.
  The public export firewall must continue to never merge "we authored and proved" with
  "we auto-harvested." All shared machinery beneath them is unified.
- **Fold `pipeline/` in as the intake/triage front-end.** Its problem-card model
  becomes the engine's front door; Brockian-authoring and Aristotle-harvest become two
  "attack modes" that feed the shared verify core. Its delegated verify step is wired to
  the shared AXLE core instead of a human-supplied boolean.
- **Standardize on `lean-4.32.2`, re-attest lazily.** One environment. The 854 Brockian
  attestations (currently `lean-4.32.0`) are re-attested opportunistically through the
  shared core by a background drain, recording the environment per attestation so nothing
  is ever falsely claimed uniform.
- **Approach: incremental "strangler" extraction.** Stand up `engine/`, then make each
  existing script delegate to it one at a time behind its existing tests, no behavior
  change, until the duplication is gone. No big-bang rewrite; no facade-only half-measure.

## 3. Architecture

A new top-level `engine/` package becomes the single source of truth for the machinery.
The existing scripts become thin callers. The two registers remain separate outputs.

```
engine/
  verify.py     # THE AXLE verification core. normalize + content_hash + fully-qualified
                # #print-axioms probe (namespace-stack aware) + strict verdict
                # (compiles clean AND axioms ⊆ ALLOWED AND no sorryAx). Pinned to
                # lean-4.32.2. Replaces the logic duplicated in axle_verify.py,
                # axle_axiom_audit.py, attest.py, cross_check.py.
  register.py   # THE derived-register gate. One PROVED definition + ALLOWED_AXIOMS,
                # as a pure function facts -> register {PROVED, CONDITIONAL, COMPUTATION,
                # DEFINITION, CONJECTURE, DISCHARGED, UNVERIFIED}. Consumed by
                # gen_registry, catalogue_domains, audit_registry_consistency,
                # verify_firewall, auto_pr, and pipeline's card register.
  audit.py      # THE honesty gate. Re-derives register invariants on committed data,
                # runs the no-theater patterns, and the overclaim/self-consistency
                # firewall — one --strict surface. Consolidates
                # audit_registry_consistency / verify_firewall / no_theater_lint.
  intake.py     # Problem-card model + triage, lifted from pipeline/core. The front door:
                # a problem (any domain/source) becomes a card, is triaged, and is routed
                # to an attack mode.
  attack.py     # Attack-mode registry. Each mode yields candidate .lean proofs into the
                # verify core: 'harvest' (Aristotle), 'author' (Brockian library), and
                # future solver modes. Modes are pluggable and independently testable.
  __init__.py
```

**Design rule:** `verify.py`, `register.py`, and `audit.py` are pure/near-pure library
modules with no scheduling, no network side effects beyond the AXLE call in `verify.py`,
and no knowledge of *which* register a proof belongs to. Routing to `theorems.json` vs
`domains.json` is the caller's concern, keeping the two-register separation explicit and
outside the shared core.

### 3.1 Unified data flow

```
                         ┌───────────────────────── engine/ ─────────────────────────┐
 problem (Brockian       │                                                            │
 target | Aristotle      │   intake.triage ──► attack.<mode> ──► verify (AXLE 4.32.2) │
 harvest | Erdős card)   │        │                 │                    │            │
        └────────────────┼────────┘                 │                    ▼            │
                         │                          │             register.derive     │
                         │                          │                    │            │
                         └──────────────────────────┼────────────────────┼───────────┘
                                                     │                    │
                              authored Brockian ◄────┘                    │────► harvest
                                     │                                    │        │
                                     ▼                                    ▼        ▼
                         registry/theorems.json                 registry/domains.json
                                     │                                    │
                                     └──────── engine.audit --strict ─────┘
                                                     │
                              export_public_registry.py │ export_public_domains.py
                                                     ▼          ▼
                              torus/public/verified-registry.json (split by source)
```

Two registers, one set of rails. The export layer is unchanged and still splits counts
by source — the honesty firewall stays exactly where it is.

## 4. Components

### 4.1 `engine.verify`

The single AXLE verification core. Public surface:

- `normalize(content) -> str` — hoist deduped imports to the top (the one canonical form).
- `content_hash(content) -> str` — `sha256(normalize(content))[:16]`. Every other module
  imports these two; they are defined exactly once.
- `qualified_decls(text) -> list[str]` — fully-qualified theorem/lemma names via a
  namespace/section stack (the fix already shipped in `axle_axiom_audit.py`; `attest.py`
  and `cross_check.py` share the bare-name bug and are corrected by delegating here).
- `axiom_audit(content, *, env="lean-4.32.2") -> AuditResult` — submit the proof plus
  fully-qualified `#print axioms` probes to AXLE `check`, parse `lean_messages.infos`,
  return `{trusted: bool|None, axioms, extra_axioms, environment, hash, detail}`.
- `compile_check(content, *, env) -> VerifyResult` — the strict compile verdict
  (`axle_client.check` normalized): compiles ∧ no errors ∧ no sorry/admit warning.

`env` defaults to `lean-4.32.2` from one constant. `axle_client.py` stays the transport;
`engine.verify` is the semantics layer above it.

### 4.2 `engine.register`

The single derived-register gate. Public surface:

- `ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}` — defined once.
- `derive(facts) -> Register` — a pure function of a small `Facts` record
  (`axioms`, `axle_verdict`, `flags{sorry, native_decide, exact_search}`, `kind`,
  `conditional_rung`) returning one of
  `{PROVED, CONDITIONAL, COMPUTATION, DEFINITION, CONJECTURE, UNVERIFIED}`. The DISCHARGED
  post-pass stays in `gen_registry` (it needs whole-registry context) but calls
  `engine.register` for the base derivation.

The exact precedence and the PROVED gate are copied verbatim from today's
`gen_registry.derive_register` so behavior does not change; the other three call sites
delete their copies and import this.

### 4.3 `engine.audit`

One `--strict` honesty surface that re-derives invariants on **committed** data (so a
hand-edited `PROVED` can't lie), runs the no-theater line patterns, and the
overclaim/self-consistency firewall. It supersedes `audit_registry_consistency.py`,
`verify_firewall.py`, and `no_theater_lint.py`, which become thin shims (or are removed
once callers move). The conveyor's `run_registry_hop` truth gate calls
`engine.audit --strict`; a failure still STOPS the hop and is never bypassed.

### 4.4 `engine.intake` + `engine.attack`

`intake` lifts `pipeline/core/schema.py` (the `ProblemCard` model) and
`pipeline/core/stages.py`/`triage.py` (triage + attack-queue) mostly verbatim.
`attack` defines a small mode interface — `attack(card) -> Iterable[Candidate]` — with
two initial modes: `harvest` (wraps the Aristotle conveyor's harvest+select) and `author`
(the Brockian library path). `pipeline/core/ledger.derive_problem_register` is rewired to
call `engine.register.derive` (with the AXLE fact supplied by `engine.verify`, not a human
boolean). The dormant CLI (`pipeline/scripts/pipeline_cli.py`) keeps working, now backed
by the live core.

## 5. Migration sequence (strangler, each step independently shippable)

Each step keeps the full suite green and the conveyor running; each is one small PR-sized
commit with a one-command rollback.

1. **`engine.verify`** — create it (lift the shipped `axle_axiom_audit` logic + the strict
   `axle_client.check` wrapper). Add unit tests. No caller changes yet.
2. **`engine.register`** — create it from `gen_registry.derive_register` verbatim + tests.
3. **Delegate the harvest verify path** — `axle_verify.py`, `axle_axiom_audit.py`,
   `cross_check.py` import `engine.verify`; delete their local `normalize`/`content_hash`/
   probe. Confirm `axle_verify.json` / `axle_axiom_audit.json` hashes are byte-identical
   on a sample before/after (hash-stability gate).
4. **Delegate the registry attest path** — `attest.py` imports `engine.verify`; this also
   fixes its namespace bare-name bug and moves it to `lean-4.32.2`. New attestations record
   `environment: lean-4.32.2`.
5. **Delegate the register gate** — `gen_registry`, `catalogue_domains`, `auto_pr`,
   `audit_registry_consistency`, `verify_firewall` import `engine.register`; delete the
   copies. `check_registry_fresh.py` must show `theorems.json` unchanged (behavior-preserving).
6. **`engine.audit`** — consolidate the three enforcers; point `run_registry_hop` at it.
7. **Fold `pipeline/`** — move `intake`/`attack`, rewire `derive_problem_register` to
   `engine.register`, wrap harvest/author as attack modes. `pipeline/` becomes a thin CLI
   over `engine/`.
8. **Lazy re-attestation drain** — a background job (modeled on the harvest audit drain)
   re-attests the 854 Brockian modules at `lean-4.32.2` through `engine.verify`, resumable
   and capped, updating `registry/attestations/*.json` and regenerating `theorems.json`
   under the truth gate.

Steps 1–6 remove the duplication and are the core of "clean engine." Steps 7–8 realize the
multi-domain vision and the env unification. The sequence can pause after any step.

## 6. Error handling & honesty invariants (must not regress)

- **Never PROVED without earning it.** A would-be PROVED that fails any leg (axioms ⊄
  ALLOWED, `sorryAx`, `sorry`/`native_decide`/`exact_search` flag, AXLE not verified)
  becomes `UNVERIFIED`, at generation *and* re-derived at audit. One definition now, but
  the same three-site enforcement (generate, audit-on-committed, export) stays.
- **Two corpora never merge in public output.** `export_public_registry.py` and
  `export_public_domains.py` stay separate; counts stay split by source.
- **AXLE outage is non-fatal.** `engine.verify` surfaces `trusted: None` on a service
  error; callers record it and move on (the conveyor's non-fatal contract is preserved).
- **Hash stability.** Because `normalize`/`content_hash` collapse to one definition,
  a migration step that changes the produced hash is a bug; step 3/4 include an explicit
  before/after hash-equality gate on a sample of proofs.
- **Env honesty.** Each attestation records the env it was actually checked under; the
  registry may be mixed-env during the drain, and that is shown, never masked.

## 7. Testing

- `engine/` modules get focused unit tests: `verify` (namespace qualification, the three
  axiom-output formats, trusted/flagged/None verdicts, mocked AXLE), `register` (every
  precedence branch of the gate), `audit` (a hand-edited PROVED is caught).
- **Behavior-preservation gates:** after each delegation step, the existing suites
  (`tests/`, `aristotle/tests/`, `pipeline/tests/`) stay green, and `check_registry_fresh.py`
  shows `theorems.json` byte-unchanged through steps 3–6.
- **Hash-stability test:** a sample of proofs produces identical `content_hash` before and
  after the `normalize` consolidation.
- The full suite must be green at every commit; the conveyor must complete a live cycle
  (`chain_ok=True`) after steps that touch it.

## 8. Non-goals

- No merge of the two corpora into one register; no change to the public registry schema
  or the export firewall.
- No change to conveyor scheduling, the LaunchAgent set, or the RAM keep-set.
- No new proof search / solver capability — `attack.py` wraps existing modes only; new
  solver modes are future specs.
- No forced, up-front bulk re-attestation — the env migration is a lazy background drain.
- No revival of dormant `scripts/` (paper/report generators, etc.) beyond what the
  delegation steps touch.

## 9. Risks

- **Hash drift** from the `normalize` consolidation silently breaking the catalogue's
  hash-match gate. Mitigated by the explicit hash-stability gate in steps 3–4.
- **Behavior drift** in the register gate when the three copies are unified (they may have
  quietly diverged). Mitigated by lifting `gen_registry.derive_register` verbatim and the
  `check_registry_fresh` byte-equality gate.
- **Re-attestation cost** for 854 modules through AXLE. Mitigated by making it a lazy,
  capped, resumable drain — never a blocker for "done."
- **Scope creep** into `pipeline/` revival. Mitigated by making steps 1–6 (the
  de-duplication) the committed core and steps 7–8 explicitly pausable.
