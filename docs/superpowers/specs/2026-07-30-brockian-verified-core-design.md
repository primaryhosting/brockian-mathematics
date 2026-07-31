# Brockian Verified Core — Design (Sub-project 1 of 3)

**Date:** 2026-07-30
**Status:** design, pending review
**Repo:** `github.com/primaryhosting/brockian-mathematics` (to be made public)

---

## 0. Program context (why this sub-project exists)

The Brockian "Curved Number Line" corpus is being turned into a serious mathematics
program. The program decomposes into three sequenced sub-projects:

| # | Sub-project | Deliverable | Rests on |
|---|-------------|-------------|----------|
| **1** | **Verified core** *(this spec)* | One canonical repo, one toolchain, every current keeper-proof building under `lake build`, `#print axioms` clean, CI green, a machine-generated **verified-theorem registry** (`registry/theorems.json`). | — |
| 2 | The paper | Preprint/monograph citing **only** registry-backed theorems, honest register labels, open problems. | Registry from #1 |
| 3 | The website | `prime-rigor-explorer` (Riemann Labs) reads the **same** registry as single source of truth; every "PROVED" badge links to a CI-green proof. | Registry from #1 |

The **registry is the linchpin**: it makes the paper and the site incapable of claiming
something the build does not verify. Sub-project 1 produces it.

### The problem being solved

Today the mathematics is credible in method but not yet independently checkable:

- The `Harmonic_Proof_Intake_Ledger.md` audits 118+ Lean/Mathlib runs with real rigor —
  it catches vacuous hypotheses, ℝ-mod collapse, Nat-division exponent traps,
  definitional theater, overtitling, ex-falso conditionals, and maintains a three-rung
  conditionality ladder. It rejects its own overclaims. This is the program's core asset.
- But: **no independent `lake build` has ever been run.** Axioms were only textually
  audited; compile hashes are "pending." (Ledger's own standing caveat.)
- The keeper proofs are **scattered across multiple toolchains** — the intake ledger
  names Lean **4.24** (run 1) and **4.28** (runs 4 / 118 / 119, pinned 4.28.0); the July
  campaign `.lean` files carry no verified pin; and the canonical repo's own
  `lakefile.toml` pins mathlib **v4.14.0** against a `lean-toolchain` of **v4.24.0** (a
  mismatch that means the repo would not build as-is) — and across **at least seven
  filesystem locations** (the repo's 6 stale modules, the
  5,411-line `catalog/brockian_all_theorems.lean`, `~/Downloads/*.lean`, `~/Desktop/*.lean`,
  `~/Desktop/SAIR-RIEMANN-LABS-PACKAGE/`, `~/Projects/QuantumProof/riemann_labs_lean_snapshot/`,
  `/Volumes/BCC-Storage/Projects/Brockian-Math/lean/`).
- The canonical repo has **2 commits from May 19**, predating the entire audited corpus
  and all July campaign work.

Sub-project 1 closes exactly this gap.

### Non-goals (YAGNI — explicitly out of scope for this sub-project)

- No paper writing (sub-project 2).
- No website changes (sub-project 3).
- **No attempt to close any open problem** — RH, Goldbach, and the unbounded Hamiltonian
  (Gate 1) stay honestly open. Their honest scaffolding is ingested; their open cores are
  left open.
- **No porting of theater** — REJECT-verdict declarations are excluded, not repaired.

---

## 1. Architecture — one repo, one toolchain, one source of truth

`primaryhosting/brockian-mathematics` becomes the single source of truth and is made
**public** (a private repo cannot be a serious public mathematics program). All other
Lean locations become one-time inputs to the ingest, then are archived (not deleted;
see §3.1).

```
brockian-mathematics/
  lean-toolchain            # latest stable Lean with an available Mathlib cache (see §2)
  lakefile.toml             # mathlib pinned to the matching stable tag
  Brockian/
    Core.lean               # φ-algebra, ray ring (ZMod 5 homs), ray-zero singularity,
                            #   Dirichlet-on-rays, fifth-roots cancellation
                            #   (CONSOLIDATES the 10× redundant φ-stacks — ledger directive)
    Admissibility.lean      # q−ν law + corollaries (q=3→1, q=5→3), master formula
                            #   count = q − #(image of gaps), singular-series positivity
                            #   + summability, naive_asymptotic_false (negative result)
    TransitionKernel.lean   # kernel double-count (totalSum_eq), constellation
                            #   classifications (twin/cousin/sexy/quadruplet), twin
                            #   exclusion, complete transition support, abstract
                            #   finite-state kernel skeleton
    Geometry.lean           # pentagon two-distance, golden diagonal = φ, cos π/5 = φ/2,
                            #   C₅ adjacency spectrum, λ₂(C₅)=2−1/φ, Aut(C₅)≅D₅,
                            #   golden_unique_to_five, D₅ group action, five-ray rigidity
    GoldbachComb.lean       # GC-1..3 local covariance kernel (gCount_eq, gCount_centered,
                            #   local_covariance); transfer conjecture named, not claimed
    Sieve.lean              # silver eigensystem (2±√2, 2), twin_pins_mod_three, no-go,
                            #   run-cap, (1,4,2) signature, ℓ−2 grammar, CRT counts,
                            #   torus period/injectivity, compatible closure
    SpectralGate1.lean      # bounded prime-Gaussian potential + multiplication-operator
                            #   self-adjointness + Weyl limit-point obligation as NAMED
                            #   hypotheses (DenselyDefinedSymmetric, not overstated);
                            #   ξ-bridge (riemannXi_eq_zero_of_nontrivial_zeta_zero,
                            #   unconditional) + RH conditional as rung-3 schema;
                            #   the unbounded Hamiltonian stays OPEN
    Brockian.lean           # root: imports all of the above
  registry/
    theorems.json           # GENERATED: build-derived fields + provenance-map fields (§5)
  provenance/
    verdicts.yaml           # HAND-AUTHORED source of truth for everything the compiled
                            #   environment cannot supply: per-declaration verdict for
                            #   SPLIT runs, ledger_run, quarantine, provenance_note, and
                            #   the closed-module list. Reviewed artifact (§3.2, §5, §6).
  scripts/
    gen_registry.py         # merge compiled-env facts + verdicts.yaml → theorems.json
    no_theater_lint.py      # grep known failure signatures → flags
  Archive/                  # retired inputs kept for reference, OUTSIDE the lean_lib globs
    catalog/                #   the old 5,411-line brockian_all_theorems.lean + JSON
  paper/                    # LEFT UNTOUCHED this sub-project (owned by sub-project 2)
  .github/workflows/ci.yml  # cache get → lake build → axiom check → registry gen → gates
  EXCLUDED.md               # every REJECT/theater declaration dropped, with failure mode
  PORT-QUEUE.md             # keeper proofs that would not port this session (see §4)
  REGISTRY.md               # human-readable rendering of theorems.json
  README.md                 # honest framing (already exists; updated)
```

**Fate of existing repo contents.** The current `Brockian/` 6 modules are superseded by
the consolidated module set and moved into the ingest (their keepers re-enter via §3;
their origin, being the repo itself, is preserved in git history — that satisfies §3.1's
"nothing deleted from origin"). `catalog/` (the 5,411-line `brockian_all_theorems.lean`
and 1.75 MB JSON) is **moved to `Archive/catalog/`** and excluded from the `lean_lib`
globs — retained as reference, not built. `paper/` is **left in place and untouched**;
sub-project 2 owns it.

**Module boundaries (isolation):** each `Brockian/*.lean` module owns one mathematical
theme. The **aspirational default** is that a module imports only `Core` (and mathlib);
this is not a hard constraint — `SpectralGate1` (ξ-bridge + RH schema) and the
cross-referencing counting modules may legitimately import a sibling, and the port
satisfies whatever the proofs actually need rather than forcing the default. A reader
should still be able to understand any module's claims without reading another's
internals. The registry generator and the no-theater lint are each standalone scripts
with a single input→output contract, independently testable.

---

## 2. Toolchain — latest stable

Standardize on the latest stable Lean + Mathlib release **that has a prebuilt Mathlib
cache available** (so `lake exe cache get` makes CI minutes, not ~1 hour of full build).
The exact tag is chosen at implementation time by checking cache availability; it is
recorded in `lean-toolchain` and `lakefile.toml` and is the acceptance gate's named pin.

The audited proofs were written against Lean 4.24–4.28 (per the ledger; July files
unpinned), and the repo currently pins mathlib v4.14.0. Porting to current mathlib **will**
break some proofs on API drift. This is expected and handled by §4's convergence rule.
We never raise `maxHeartbeats` to hide a hang, never add an axiom to force a close, and
never fake a build to get a green.

---

## 3. Ingest & triage pipeline

### 3.1 Discovery and deduplication

Collect every `.lean` file from the known locations. Compute md5; drop byte-identical
duplicates (the ledger already recorded many). Source files are copied into a one-time
`_ingest/` staging area (git-ignored) so originals on disk are never mutated; nothing is
deleted from its origin.

### 3.2 Verdict filter (only keepers are eligible)

The intake ledger records verdicts **per run (file)**, and a large fraction of admitted
runs are **SPLIT** (ADMIT one part, REJECT another) described in *prose*, not as a
machine-readable per-declaration list — e.g. run 22's "placeholder suite," run 50's
"zero-determinant suite," run 53's "multiplicity-one suite" are named by theme, not by
exhaustive declaration name. **The ledger alone therefore cannot mechanically decide
ADMIT vs EXCLUDE for every declaration in a SPLIT run.**

Resolution: a **hand-authored `provenance/verdicts.yaml`** is the source of truth for the
per-declaration verdict. It is produced during ingest by reading the ledger prose and the
`.lean` source together, one entry per declaration in a SPLIT (or otherwise
non-trivially-classified) run, each carrying `verdict` (admit/exclude), `failure_mode`
(for excludes), and the provenance fields of §5. Whole-run ADMIT and whole-run REJECT need
no per-declaration entry (the run-level verdict applies). `verdicts.yaml` is a reviewed
artifact — it is checked in, and its exclude entries must each cite the ledger line that
justifies them.

Then:

- **ADMIT / keeper** declarations → eligible for ingest.
- **REJECT / theater / superseded / duplicate** declarations → **excluded**, and rendered
  into `EXCLUDED.md` (generated from `verdicts.yaml`) with the declaration name and its
  named failure mode (definitional theater, degenerate witness, ℝ-mod collapse,
  Nat-division exponent, overtitling, ex-falso conditional, instance-filled Prop,
  modus-ponens, etc.). The exclusion list is itself an auditable artifact — dropping
  theater silently would violate the program's ethic.

### 3.3 Consolidation

Collapse the 10×-redundant φ / ray stack into one `Core.lean`, keyed on
namespace + theorem-name set (the ledger's explicit consolidation directive). The
canonical anchors are runs 97 / 103 / 112 / 119; redundant re-proofs are dropped (their
statement-stability value is noted in `EXCLUDED.md` as "corroborating replication," not
deleted from history).

### 3.4 Port

Port eligible declarations to the target toolchain; repair API drift. Pin any stray
`exact?` search tactics to named lemmas before a declaration may enter register PROVED
(ledger obligation; worst offenders runs 44 ×29, 113 ×17).

### 3.5 Register tagging

Every surviving declaration is tagged with exactly one register (§4).

---

## 4. Register discipline as enforced CI gates

Four ledger-native registers. CI enforces them mechanically against the **actually
compiled environment**, so a label cannot lie about a build.

| Register | Definition | CI gate |
|----------|------------|---------|
| **PROVED** | sorry-free **and** `#print axioms ⊆ {propext, Classical.choice, Quot.sound}` **and** no `native_decide` / `Lean.ofReduceBool` **and** no residual `exact?` | CI **fails** the PR if any PROVED-tagged decl violates any clause |
| **COMPUTATION** | `decide` / `native_decide` finite checks | auto-demoted here; never PROVED |
| **CONDITIONAL** | depends on a named hypothesis; **must** record its rung: `classical` (true, absent from mathlib) / `literature` (published, borrowed) / `open` (open-strength schema) | schema-rung conditionals are never counted as evidence |
| **CONJECTURE** | a `def` / Prop container, never a `theorem` | must not be typed as a proof |

**No-theater lint** (`scripts/no_theater_lint.py`) additionally flags known failure
signatures for human review, independent of the build: `:= 0` operators asserted
self-adjoint, `% (2 * π)`, Nat `^(1/2)` / fractional-literal exponents, `True`-typed Prop
fields, free unconstrained `Prop` fields, `sorry`, `admit`, and theorem names that borrow a
bigger theorem's name (overtitling — heuristic, human-confirmed).

**Convergence rule (honesty over completeness).** A keeper proof that will not port to the
target toolchain this session is marked `status: port-pending`, recorded in
`PORT-QUEUE.md` with the blocking error, and **kept out of the compiling core** so `lake
build` is always green. It is never silently kept, never faked, never force-closed. The
repo converges on the genuinely buildable set and reports the remainder truthfully.

**Quarantine flag.** The ledger notes the run-119 consolidated package is "quarantine-side"
— machine-checking it proves the *method*, and does not discharge the book's separate
commitment (§19.10) to formalize its four core control theorems. Every registry entry
carries a boolean `quarantine` (sourced from `verdicts.yaml`, §5). Nothing quarantined may
be surfaced as a headline claim by sub-projects 2 or 3.

**Closed-module tag.** A module is "fully closed" (no `sorry`/`admit` tolerated; the
no-theater lint blocks on any) iff it is listed under `closed_modules:` in
`verdicts.yaml`. The initial closed set is the run-119 modules 1/2/5, which map to
`Brockian/Core.lean`, `Brockian/Admissibility.lean`, and `Brockian/TransitionKernel.lean`
respectively. `SpectralGate1.lean` is explicitly **not** closed (its Hamiltonian core is
honestly open).

---

## 5. Data flow — the registry

```
Brockian/*.lean ──lake build──► compiled environment ─┐
                                                       ├─► scripts/gen_registry.py ─► registry/theorems.json ─► REGISTRY.md
provenance/verdicts.yaml ─────────────────────────────┘         │                          │
  (ledger_run, quarantine,                                       │                          ├─► sub-project 2 (paper)
   provenance_note, verdict)                                     │                          └─► sub-project 3 (website)
```

`gen_registry.py` has **two input sources**, and each field's origin is explicit:

- **Build-derived (cannot disagree with the build):** `name`, `kind`, `statement`,
  `module`, `source` file+line, `axioms` (from `#print axioms`), `flags`
  (`native_decide` / `sorry` / `exact_search`), and therefore the **`register`** itself —
  `register` is *computed* from `axioms` + `flags` + the `conditional_rung`, never
  hand-asserted, so no declaration can wear a PROVED label its build does not earn.
- **Provenance-map (from `verdicts.yaml`, not recoverable from the environment):**
  `ledger_run`, `quarantine`, `provenance_note`, and the `conditional_rung` value for
  CONDITIONAL entries. These are human-maintained and reviewed; the generator merges them
  by declaration name and errors if a compiled PROVED/CONDITIONAL declaration is missing
  its required provenance entry.

**Extraction scope:** `gen_registry.py` extracts **all declarations** in the `Brockian`
namespace — `theorem`/`lemma` *and* `def`/Prop containers — so CONJECTURE-register
containers (which are `def`s by §4) appear in the registry alongside proved theorems.

`theorems.json` schema (per entry):

```json
{
  "name": "Brockian.Admissibility.universal_admissibility_count",
  "kind": "theorem",
  "module": "Brockian.Admissibility",
  "statement": "<pretty-printed type>",
  "source": { "file": "Brockian/Admissibility.lean", "line": 71 },
  "register": "PROVED",
  "axioms": ["propext", "Classical.choice", "Quot.sound"],
  "flags": { "native_decide": false, "sorry": false, "exact_search": false },
  "conditional_rung": null,
  "quarantine": true,
  "ledger_run": "74 (a0ce…) / 119 module 2",
  "provenance_note": "citation-grade ZMod statement of the q−ν law"
}
```

The register is **derived**, not hand-asserted: `gen_registry.py` computes it from the
axiom list + flags, so the JSON cannot disagree with the build.

---

## 6. Testing & verification

The build is the primary test. Verification layers:

1. **`lake build` green** on the target toolchain (CI + local).
2. **Axiom assertion** per PROVED theorem: `gen_registry.py` runs `#print axioms` (via
   `lake env lean --run` on a generated probe, or Lean metaprogram) and the CI gate fails
   if any PROVED decl's axiom set exceeds the allowed three.
3. **Registry round-trip test**: every PROVED entry maps to a real declaration that
   compiled this run; no orphan or stale entries.
4. **No-theater lint** runs in CI as a non-blocking report (blocking only for `sorry` /
   `admit` inside modules tagged as fully closed, e.g. run-119 modules 1/2/5).
5. **Reproducibility**: CI records the `lake build` log and the resolved mathlib rev/hash
   — the compile hashes the ledger has been waiting on finally enter the record.

---

## 7. Risks & mitigations

| Risk | Mitigation |
|------|------------|
| Large API drift (v4.14→current) breaks many proofs | Convergence rule (§4): port-pending + PORT-QUEUE, build stays green; converge on the buildable set, report the rest. |
| No Mathlib cache for the newest tag → ~1h builds | §2: pick the newest stable tag that *has* a cache; record it as the pin. |
| Verdict cross-referencing is manual/error-prone at 118 runs | Ledger is already structured per-run; ingest keys on it and every inclusion/exclusion is written to `EXCLUDED.md` / registry `ledger_run` for audit. |
| Accidental secret in repo before making public | Pre-publish scan (`git secrets` / grep for key patterns); repo is math-only, 2 clean commits — low risk, but gated. |
| Over-consolidation loses a genuinely distinct proof | Consolidation keys on namespace + theorem-name set; anything ambiguous is kept, not merged; `EXCLUDED.md` records every drop with reason. |

---

## 8. Acceptance criteria

Sub-project 1 is done when:

- [ ] `primaryhosting/brockian-mathematics` is public, on one recorded toolchain pin.
- [ ] A **pre-publish secret scan** (grep for key patterns + `git secrets`-style check over
      full history) passes before the repo is made public.
- [ ] `lake build` is green locally and in CI (cache-backed).
- [ ] **Must-port coverage** — the build is *not* trivially-empty: it contains, in register
      PROVED (or, where the ledger admits them as such, CONDITIONAL/COMPUTATION with the
      correct rung), the program's headline keepers:
      the q−ν admissibility law with its q=3 and q=5 corollaries (runs 74/49);
      `golden_unique_to_five` (run 73); `λ₂(C₅)=2−1/φ` (run 88); `Aut(C₅)≅D₅` and the
      pentagon golden-diagonal / two-distance geometry (runs 54/70/16); Dirichlet-on-rays
      (run 97); the full constellation/transition classification + twin exclusion (runs
      7/31/117); GC-1..3 Goldbach covariance (intake 18); and the silver-gap eigensystem
      (intake 18). Any of these that will not port is a **release-blocking** PORT-QUEUE
      item requiring explicit human sign-off to defer — unlike ordinary port-pending decls.
- [ ] Every declaration in `Brockian/` carries a derived register; no PROVED decl violates
      its gate; `#print axioms` recorded for each.
- [ ] `registry/theorems.json` is generated by CI and committed; `REGISTRY.md` renders it;
      every compiled PROVED/CONDITIONAL decl has its required `verdicts.yaml` provenance
      entry (generator errors otherwise).
- [ ] `EXCLUDED.md` lists every dropped REJECT/theater/superseded declaration with its
      named failure mode; a **reverse check** confirms every exclude entry in
      `verdicts.yaml` renders to `EXCLUDED.md` and vice-versa (no silent drops).
- [ ] `PORT-QUEUE.md` lists every port-pending keeper with its blocking error.
- [ ] No `sorry`/`admit` in modules on the `closed_modules` list; open cores (Hamiltonian,
      RH, Goldbach transfer) are explicitly and honestly marked open, not faked.
- [ ] The compile log + resolved mathlib hash are recorded (closes the ledger's standing
      "compile hashes pending" caveat).

---

## 9. Open questions deferred to the plan

- Exact target toolchain tag (chosen by cache availability at implementation time).
- Whether `gen_registry.py` extracts axioms via a Lean metaprogram or `#print axioms`
  probe parsing (implementation detail; both satisfy §6.2).
- Ingest orchestration shape (single pass vs per-module agents) — a plan/execution
  concern, not a design concern.
