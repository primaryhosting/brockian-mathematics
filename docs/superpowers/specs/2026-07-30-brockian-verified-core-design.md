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
- The keeper proofs are **scattered across three toolchains** (Lean 4.24 / 4.28 / 4.30)
  and **at least seven filesystem locations** (the repo's 6 stale modules, the
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
    theorems.json           # GENERATED from the compiled environment (see §5)
  scripts/
    gen_registry.py         # extract declarations + #print axioms → theorems.json
    no_theater_lint.py      # grep known failure signatures → flags
  .github/workflows/ci.yml  # cache get → lake build → axiom check → registry gen → gates
  EXCLUDED.md               # every REJECT/theater declaration dropped, with failure mode
  PORT-QUEUE.md             # keeper proofs that would not port this session (see §4)
  REGISTRY.md               # human-readable rendering of theorems.json
  README.md                 # honest framing (already exists; updated)
```

**Module boundaries (isolation):** each `Brockian/*.lean` module owns one mathematical
theme and imports only `Core` (and mathlib). A reader can understand any module's claims
without reading the internals of another. The registry generator and the no-theater lint
are each standalone scripts with a single input→output contract, independently testable.

---

## 2. Toolchain — latest stable

Standardize on the latest stable Lean + Mathlib release **that has a prebuilt Mathlib
cache available** (so `lake exe cache get` makes CI minutes, not ~1 hour of full build).
The exact tag is chosen at implementation time by checking cache availability; it is
recorded in `lean-toolchain` and `lakefile.toml` and is the acceptance gate's named pin.

The audited proofs were written against Lean 4.14→4.28. Porting to current mathlib **will**
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

Cross-reference each declaration against the intake ledger's verdict for its run:

- **ADMIT / keeper** content → eligible for ingest.
- **REJECT / theater / superseded / duplicate** content → **excluded**, and recorded in
  `EXCLUDED.md` with the declaration name and its named failure mode (definitional theater,
  degenerate witness, ℝ-mod collapse, Nat-division exponent, overtitling, ex-falso
  conditional, instance-filled Prop, modus-ponens, etc.). The exclusion list is itself an
  auditable artifact — dropping theater silently would violate the program's ethic.

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
carries a boolean `quarantine`. Nothing quarantined may be surfaced as a headline claim by
sub-projects 2 or 3.

---

## 5. Data flow — the registry

```
Brockian/*.lean
      │  lake build  (target toolchain, cache-backed)
      ▼
compiled environment  ──►  scripts/gen_registry.py
                               │   (per declaration: name, kind, formal statement,
                               │    module, source file+line, #print axioms output,
                               │    native_decide?, sorry?, originating ledger run,
                               │    quarantine flag → derived register)
                               ▼
                        registry/theorems.json  ──►  REGISTRY.md (human view)
                               │
                               ├─►  sub-project 2 (paper theorem environments)
                               └─►  sub-project 3 (website PROVED badges + proof links)
```

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
- [ ] `lake build` is green locally and in CI (cache-backed).
- [ ] Every declaration in `Brockian/` carries a derived register; no PROVED decl violates
      its gate; `#print axioms` recorded for each.
- [ ] `registry/theorems.json` is generated by CI and committed; `REGISTRY.md` renders it.
- [ ] `EXCLUDED.md` lists every dropped REJECT/theater/superseded declaration with its
      named failure mode; `PORT-QUEUE.md` lists every port-pending keeper with its error.
- [ ] No `sorry`/`admit` in modules declared closed; open cores (Hamiltonian, RH, Goldbach
      transfer) are explicitly and honestly marked open, not faked.
- [ ] The compile log + resolved mathlib hash are recorded (closes the ledger's standing
      "compile hashes pending" caveat).

---

## 9. Open questions deferred to the plan

- Exact target toolchain tag (chosen by cache availability at implementation time).
- Whether `gen_registry.py` extracts axioms via a Lean metaprogram or `#print axioms`
  probe parsing (implementation detail; both satisfy §6.2).
- Ingest orchestration shape (single pass vs per-module agents) — a plan/execution
  concern, not a design concern.
