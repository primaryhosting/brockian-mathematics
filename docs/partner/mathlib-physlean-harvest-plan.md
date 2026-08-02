# Mathlib + PhysLean/Physlib Harvest Plan

**Verification at scale for QuantumProof / IonQ and Brockian Verified Core**  
**Audience:** Riemann Labs operators, QuantumProof engineering, partner technical diligence  
**Date:** 2026-08-02  
**Status:** Planning only — does not modify Lean sources or registry counts  
**Classification:** Partner-ready infrastructure plan (non-confidential)

---

## 0. Thesis

Do **not** hand-formalize the mathematical universe. Scale by **ingesting community-verified Lean corpora** (Mathlib, Physlib / former PhysLean + Lean-QuantumInfo), then running them through **our honesty stack**:

```
community corpus  →  pin  →  lake build  →  axiom gate  →  AXLE re-attest
                  →  derived register  →  firewall  →  deploy surface
```

| Layer | Role |
|-------|------|
| **Mathlib** | Standard math substrate (number theory, algebra, spectral/operator, analysis) |
| **Physlib** | Physics + quantum-information digitalization ([github.com/leanprover-community/physlib](https://github.com/leanprover-community/physlib), [physlib.io](https://physlib.io)) — merge of **PhysLean** (ex HepLean) and **Lean-QuantumInfo** |
| **Brockian core** | Differentiated theorems, multi-prover ops, derived registers, no-theater discipline |
| **Deploy** | QuantumProof/IonQ formal artifacts; sieve/Gate-1/spectral research; registry explorer |

**Hard honesty rules (unchanged):**

- PROVED is never hand-painted; it is derived from axioms + independent check.
- RH, global Goldbach transfer, full unbounded ESA remain **scaffolded / CONDITIONAL / CONJECTURE** until closed.
- Harvested theorems inherit **source provenance** (`mathlib`, `physlib:QuantumInfo`, `physlib:Physlib`, `brockian`).
- Marketing counts always cite **registry export + commit hash**.

**Related local docs:**

- [`docs/MATHLIB-UPSTREAM-CANDIDATES.md`](../MATHLIB-UPSTREAM-CANDIDATES.md) — what Brockian might *give* Mathlib
- [`docs/MATHLIB-PR-BLUEPRINTS.md`](../MATHLIB-PR-BLUEPRINTS.md) — PR-sized extraction spine
- [`docs/DEPENDENCY-FIREWALL.md`](../DEPENDENCY-FIREWALL.md) — overclaim audit
- [`docs/partner/2026-08-02-verified-intelligence-strategy-brief.md`](./2026-08-02-verified-intelligence-strategy-brief.md) — Phase D “scale harvest”
- [`REGISTRY.md`](../../REGISTRY.md) — live SSOT summary (regenerate before partner numbers)

**Current pin (Brockian tip family):**

| Item | Value |
|------|--------|
| Lean | `leanprover/lean4:v4.32.0` (`lean-toolchain`) |
| Mathlib | `v4.32.0` (`lakefile.toml` / `lake-manifest.json`) |
| Physlib pin (upstream) | Same Lean **v4.32.0** + Mathlib **v4.32.0** (as of 2026-08-02) — *aligned* |
| Registry snapshot (order of magnitude) | PROVED ~1477 · DEFINITION ~306 · CONDITIONAL ~21 · DISCHARGED 6 · CONJECTURE 1 |

---

## 1. What to IMPORT vs RE-PROVE vs RE-ATTEST

Three actions. Misclassifying a theorem is the primary source of bloat and axiom pollution.

### 1.1 Decision matrix

| Action | Meaning | When | Register path | Cost / risk |
|--------|---------|------|---------------|-------------|
| **IMPORT** | Depend on upstream via Lake; use declarations in new Brockian/QP modules | Upstream already has the API; statement matches need; no narrative packaging required | Upstream not counted as Brockian PROVED; **consumer** lemmas may be attested | Low code; **high pin-coupling** |
| **RE-PROVE** | Write a local proof of a statement that exists (or should exist) upstream, or of a Brockian-specific packaging | Gap in Mathlib/Physlib; need a different statement shape; or generalization from Fin 5 / project names | Local PROVED after triple gate | High effort; **duplication risk** |
| **RE-ATTEST** | Independently re-check an upstream (or extracted) declaration through AXLE + axiom gate + registry provenance | Want partner-facing “we verified this statement at env X” without owning the proof body long-term | **External / harvested** attestation class (see §4.4); not inflated into “Brockian invented this” | Medium ops; **statement-fidelity** critical |

### 1.2 Default policy

```
IF   Mathlib/Physlib has a stable declaration with the right statement
AND  we only need it as infrastructure
THEN IMPORT (focused modules; no whole-library import theater)

ELSE IF we need a different interface, bridge lemma, or project packaging
THEN RE-PROVE the *delta* only; IMPORT the rest

ELSE IF partner diligence requires independent verification of a community theorem
THEN RE-ATTEST (pin commit + statement hash + AXLE env)

NEVER re-prove Mathlib lemmas just to grow PROVED count.
NEVER import PhyslibAlpha as production substrate without quarantine.
```

### 1.3 Classification guide by domain

#### Mathlib-facing (Brockian overlaps)

| Topic | Prefer | Notes |
|-------|--------|-------|
| `ZMod`, CRT, `Finset.card`, basic modular arithmetic | **IMPORT** | Foundation of admissibility/sieve; only re-prove *admissible-set* packaging |
| Finite cyclic characters / roots of unity (general `n`) | **IMPORT** if present; else **RE-PROVE** generalized form | See upstream candidates §14–15: prefer `ZMod n` over `Fin 5` theater |
| Graph theory (`SimpleGraph`, cycle graphs) | **IMPORT** structure; **RE-PROVE** spectral closed forms as needed | Cycle spectrum may stay local until Mathlib has circulant API |
| `LinearPMap`, adjoint, formal adjoint | **IMPORT** Mathlib base; **RE-PROVE** missing `IsSymmetric` / deficiency / ESA spine | Highest upstream *gift* to Mathlib ([MATHLIB-UPSTREAM-CANDIDATES](../MATHLIB-UPSTREAM-CANDIDATES.md) §1–10) |
| Singular series / Euler products | **IMPORT** `Multipliable`/`tprod` analysis; **RE-PROVE** HL-local factors | Do not upstream “limit-or-zero” packaging as-is |
| RH / Goldbach global / Hilbert–Pólya | **Neither** as PROVED | Schema + CONDITIONAL only |

#### Physlib / QuantumInfo-facing (IonQ / QuantumProof)

| Topic | Prefer | Notes |
|-------|--------|-------|
| Density matrices, pure/mixed states | **IMPORT** `QuantumInfo.States.*` | Substrate for entropy / sampling models |
| CPTP channels, matrix maps | **IMPORT** `QuantumInfo.Channels.*` | Hybrid KEM / noise models |
| von Neumann / relative entropy, DPI, SSA | **IMPORT** `QuantumInfo.Entropy.*`; **RE-ATTEST** partner-critical lemmas | Direct path to “formal statements under assumptions” for randomness / distinguishability |
| Unitary operators | **IMPORT** `QuantumInfo.Operators.Unitary` | Gate models; finite-dimensional first |
| Capacity / resource theory / Stein-type results | **IMPORT** + **RE-ATTEST** named lemmas used in demos | Cite Physlib papers (e.g. generalized quantum Stein’s lemma arXiv:2510.08672) |
| QM free particle, HO, hydrogen (pedagogy) | **IMPORT** selectively; **not** production QP path | Useful for demos; avoid claim inflation |
| Unbounded operators / spectral theory in Physlib QM | **IMPORT** for language alignment; **RE-PROVE** Gate-1 bridges in Brockian terms | Map to `Weyl*` / `LinearPMap` stack carefully |
| PhyslibAlpha | **Do not IMPORT into production** | Lower review bar; harvest only as **staging / candidate** after promotion to Physlib |

#### Brockian-only (do not replace with harvest)

| Keep local (RE-PROVE / maintain) | Reason |
|----------------------------------|--------|
| Admissibility q−ν law, k-tuple CRT, HL criterion packaging | Differentiated finite sieve grammar |
| C5/D5 spectral multiplicities, golden uniqueness | Research narrative + TQC bridge; not Mathlib-ready as story |
| Goldbach local covariance kernel | Local PROVED; transfer stays CONJECTURE |
| Weyl/Gate-1 campaign modules | Operator-theory program; partial Mathlib extractability |
| Registry / attestation / no-theater | Process product — not replaceable by import |

### 1.4 Explicit anti-patterns

| Anti-pattern | Why it fails |
|--------------|--------------|
| Counting Mathlib theorems as Brockian PROVED | Destroys honesty brand |
| Re-proving `Finset.card_image_of_injOn` style lemmas | Bloat + drift from Mathlib API |
| Importing all of Physlib for one entropy lemma | Disk, build time, pin friction |
| Re-attesting PhyslibAlpha with PROVED badges | Axiom / sorry / quality pollution |
| Claiming IonQ “quantum verified” because QuantumInfo imported | Statement must match the *model* in the demo |

---

## 2. Priority modules — IonQ / PQC / quantum-info bridge

**Goal:** End-to-end demos where a **small formal security or entropy claim** gets a registry badge under stated assumptions — not “we solved quantum.”

Aligned with partner brief Phase C: *1–2 formal security/entropy lemmas with registry badges*.

### 2.1 Physlib targets (consume first)

Physlib is two build targets sharing one repo and (currently) the same Lean/Mathlib pin:

| Target | Path | Harvest priority for QP/IonQ |
|--------|------|------------------------------|
| **QuantumInfo** | `QuantumInfo/` | **P0** — primary substrate |
| **Physlib** (physics) | `Physlib/` | **P1** for QM operators; **P2** for HEP/QFT/etc. |
| **PhyslibAlpha** | `PhyslibAlpha/` | **P3 quarantine only** |

#### P0 — QuantumInfo (IonQ/QP wedge)

| Module area | Path | Why harvest | Action |
|-------------|------|-------------|--------|
| States (pure/mixed/ensemble/entanglement) | `QuantumInfo/States/**` | Density-operator language for entropy & sampling models | IMPORT core defs |
| Channels (CPTP, matrix maps, dual, pinching) | `QuantumInfo/Channels/**` | Noise / hybrid channel models | IMPORT |
| Entropy (von Neumann, relative, DPI, SSA) | `QuantumInfo/Entropy/**` | **Primary partner lemmas** — distinguishability, data-processing | IMPORT + RE-ATTEST selected theorems |
| Unitary operators | `QuantumInfo/Operators/Unitary.lean` | Finite unitary evolution / gate models | IMPORT |
| Measurements | `QuantumInfo/Measurements/**` | Measurement model statements | IMPORT selective |
| Capacity / ResourceTheory | `QuantumInfo/Capacity/**`, `ResourceTheory/**` | Longer-horizon QKD / resource claims | IMPORT map; attest later |
| ForMathlib | `QuantumInfo/ForMathlib/**` | Overlap / upstream queue with Mathlib | Prefer Mathlib if landed; else IMPORT via QI |
| ClassicalInfo | `QuantumInfo/ClassicalInfo/**` | Classical entropy baselines for hybrid claims | IMPORT as needed |

#### P1 — Physlib QuantumMechanics (alignment with Gate-1 / spectral narrative)

| Module area | Path | Why | Action |
|-------------|------|-----|--------|
| Hilbert spaces | `Physlib/QuantumMechanics/HilbertSpaces/**` | Shared language with Brockian operator work | IMPORT carefully |
| Unbounded operators | `Physlib/QuantumMechanics/Operators/Unbounded.lean` | Overlaps Gate-1 ESA program | Map vs `Brockian.Weyl*`; avoid double stacks |
| Spectral theory | `Physlib/QuantumMechanics/Operators/SpectralTheory/**` | Spectral packaging | IMPORT or bridge |
| Multiplication / position / momentum | `Operators/Multiplication`, `Position`, `Momentum` | Free-particle / Fourier narrative | Align with `WeylFourierMultiplier`, free Laplacian |
| Free particle / HO | `FreeParticle/**`, `HarmonicOscillator/**` | Demo physics; not PQC | Optional IMPORT for demos |

#### P2 — Defer (not QP-critical)

Classical field theory, QFT, cosmology, string theory, fluids, condensed matter (except any future topological-phase formalization explicitly scoped) — **map only**, do not pull into QuantumProof builds.

### 2.2 Mathlib targets for quantum/PQC bridge

| Mathlib area (conceptual) | Use in QP/IonQ path |
|---------------------------|---------------------|
| Linear algebra, matrices, `Matrix`, eigenvalues (finite-dim) | Classical crypto + finite quantum models |
| Probability / measure (where present) | Sampling / entropy hypotheses |
| Analysis: norms, continuous linear maps | Channel/operator norms |
| Number theory: modular arithmetic, finite fields | PQC algorithm models (Kyber-style modulars, etc.) — **model math**, not “NIST approved” |
| Cryptography formalizations (if/when in Mathlib or separate) | Only when pinned and reviewed |

### 2.3 QuantumProof formal artifact menu (harvest-backed)

Ship **small** propositions; each gets registry row + attestation:

| Demo class | Example statement shape (informal) | Substrate | Register discipline |
|------------|------------------------------------|-----------|---------------------|
| **Entropy bound** | Under model `M`, von Neumann entropy of state `ρ` satisfies … | QI Entropy | PROVED only if model is closed; else CONDITIONAL on `M` |
| **DPI / processing** | Channel `N` does not increase distinguishability (DPI form) | QI Entropy/DPI | RE-ATTEST core + thin wrapper |
| **Unitary invariance** | Entropy invariant under unitary conjugation | QI + Unitary | IMPORT + wrapper |
| **Hybrid composition** | Classical×quantum hybrid model satisfies property `P` | ClassicalInfo + Channels | Explicit hybrid def; no overclaim |
| **Finite sampling model** | Extractor / min-entropy model lemma | Mathlib + QI | Assumptions explicit |

**IonQ job path (operational):**

1. QPU or hybrid job produces classical post-process data.  
2. Claim is formalized about the **named model** (not the physical device).  
3. Lean checks model lemma → AXLE → registry badge.  
4. Partner language: *provable under stated assumptions* — same grammar as RH scaffolding.

### 2.4 Non-goals (IonQ/QP)

- Formalizing the entire device stack or firmware.  
- Claiming post-quantum “compliance” solely from Mathlib imports.  
- Using Fibonacci/D5 formal narrative as a substitute for NIST PQC proofs (research bridge only).

---

## 3. Priority modules — sieve / admissibility / spectral / Gate-1

**Goal:** Grow Brockian verified core where it is differentiated, while **importing** Mathlib substrate and **extracting** reusable operator theory upward.

### 3.1 Mathlib harvest map (consume)

| Mathlib domain | Relevant Brockian consumers | Harvest action |
|----------------|----------------------------|----------------|
| **Number theory / modular** — `ZMod`, CRT, primes, `Nat.ModEq` | `Admissibility*`, `Sieve`, `SingularSeries*`, `Goldbach*` | IMPORT; stop local re-proof of generic card/CRT facts |
| **Finite sets / combinatorics** — `Finset`, `Fintype` | Admissibility counts, twin filters | IMPORT |
| **Algebra / group theory** — cyclic groups, dihedral, representation basics | `Automorphism*`, `D5*`, `AffineSymmetry`, Galois modules | IMPORT group API; keep C5 packaging local until generalized |
| **Linear algebra / matrices** | Spectral, Laplacian modes | IMPORT |
| **Analysis / operator theory** — `LinearPMap`, adjoints, Hilbert spaces, CLMs | Entire `Weyl*` campaign | IMPORT base; RE-PROVE missing symmetric/deficiency/ESA API |
| **Fourier / analysis** | Free Laplacian, Plancherel scaffolds | IMPORT what exists; scaffold CONDITIONAL remainder |
| **Graph theory** | Cycle graphs, connectivity | IMPORT `SimpleGraph`; spectral closed forms local or future upstream |

### 3.2 Brockian priority clusters (maintain / attack)

Ordered for **research progress + Mathlib extractability**, not for marketing count:

#### Cluster A — Sieve / admissibility (stable PROVED base)

| Modules (local) | Status posture | Harvest interaction |
|-----------------|----------------|---------------------|
| `Admissibility`, `AdmissibilityCRT`, `AdmissibilityCRTGeneral` | PROVED kernel | Thin imports from Mathlib CRT; no re-prove |
| `AdmissibilityKTuple`, `AdmissibilityDiagonal`, `AdmissibilityHLCriterion` | PROVED packaging of HL grammar | Keep; upstream *generic* card lemmas only |
| `Sieve`, twin admissibility | Finite card facts | Extract Mathlib-friendly forms (see candidates §13) |
| `SingularSeries*`, `SingularSeriesWire` | Local factors + positivity under admissibility | Redesign products around Mathlib `Multipliable` before upstream |

**Milestone focus:** hygiene + focused imports + optional Mathlib PRs for CRT product-cardinality — **not** prime-distribution claims.

#### Cluster B — Spectral / pentagon / D5 (research + TQC narrative)

| Modules | Status posture | Harvest interaction |
|---------|----------------|---------------------|
| `Spectral`, `CycleSpectrumFamily`, `C5SpectralMultiplicities` | PROVED finite spectra | Generalize toward Mathlib cycle spectrum API |
| `D5Representation`, `D5Isotypic`, `D5FourierInversion`, `D5LaplacianModes`, `D5CharacterTable` | PROVED finite Fourier/isotypics | IMPORT roots-of-unity; RE-PROVE only packaging |
| `Automorphism`, `AutomorphismFull`, `AffineSymmetry` | PROVED Aut(C5)≃D5 style | Future Mathlib PR for `Aut(C_n)≃D_n` |
| `GaloisWhyFive`, `Galois*`, `Metallic*`, golden uniqueness | Algebraic “why five” | Mathlib field/minpoly IMPORT; keep classification local |

#### Cluster C — Gate-1 / Weyl / Schrödinger (open cores honest)

| Modules | Status posture | Harvest interaction |
|---------|----------------|---------------------|
| `WeylOperator`, `WeylCayley`, `WeylClosure`, `WeylEssSelfAdjoint` | Structural PROVED + API gaps | **Highest Mathlib upstream value** (IsSymmetric, deficiency, closability) |
| `WeylFreeLaplacian*`, `FreeLaplacianPlancherel`, `WeylFourierMultiplier` | Partial / CONDITIONAL Fourier ESA | IMPORT Mathlib Fourier where available; Physlib QM alignment |
| `WeylKato*`, `WeylSchrodinger*`, `WeylLimitPoint*`, `WeylDichotomy*` | Scaffold + CONDITIONAL regularity/perturbation | Do **not** harvest “closed ESA” from Physlib without statement match |
| `SpectralGate1`, `RiemannScaffold`, `RiemannXi*` | Scaffold; RH CONDITIONAL | Never import as PROVED RH |

**Pipeline cards already aligned:**

- `pipeline/catalog/quantum/quantum-free-laplacian-plancherel.json`
- `pipeline/catalog/physics/physics-schrodinger-esa-bridge.json`
- `pipeline/catalog/math/math-gate1-lp-continuous-bounded.json` (if present / seed)

### 3.3 Suggested attack order (Gate-1 + spectral)

1. **Mathlib LinearPMap gap audit** — what already landed since candidates doc (2026-08-01).  
2. **Extract PR spine 1–5** from [MATHLIB-PR-BLUEPRINTS](../MATHLIB-PR-BLUEPRINTS.md) *or* keep local until PR-ready (parallel tracks).  
3. **Import-minimization** of Brockian modules (`import Mathlib` → focused imports) — reduces bloat and clarifies harvest.  
4. **Physlib QM Unbounded / SpectralTheory crosswalk** — table of declaration equivalences vs `Weyl*`.  
5. **CONDITIONAL discharge only with named classical hypotheses** — never silent axiomatization.

### 3.4 Bidirectional harvest

| Direction | Content |
|-----------|---------|
| **In** (community → Brockian) | Mathlib number theory + operator base; Physlib QuantumInfo entropy/channels; selective Physlib QM |
| **Out** (Brockian → Mathlib) | Symmetric `LinearPMap` API, deficiency/range, ZMod counting, cyclic Fourier, cycle spectra ([UPSTREAM-CANDIDATES](../MATHLIB-UPSTREAM-CANDIDATES.md)) |
| **Out** (Brockian → Physlib) | Only if physics-framed and maintainer-aligned; prefer Mathlib for pure math |

---

## 4. Operational pipeline: pin → lake → attestation → register

### 4.1 Topology

```
┌──────────────┐   rev pin    ┌─────────────────┐
│ Mathlib tag  │─────────────►│ lakefile.toml   │
│ Physlib rev  │─────────────►│ lean-toolchain  │
└──────────────┘              │ lake-manifest   │
                              └────────┬────────┘
                                       │ lake exe cache get && lake build
                                       ▼
                              ┌─────────────────┐
                              │ Build artifacts │
                              │ #print axioms   │
                              └────────┬────────┘
                                       │ scripts/attest.py / settle.py
                                       ▼
                              ┌─────────────────┐
                              │ AXLE env check  │  lean-4.32.0 (or dual)
                              └────────┬────────┘
                                       │
                                       ▼
                              ┌─────────────────┐
                              │ attestations/   │
                              │ certificates/   │
                              └────────┬────────┘
                                       │ scripts/gen_registry.py
                                       ▼
                              ┌─────────────────┐
                              │ theorems.json   │──► REGISTRY.md / observatory / paper
                              │ firewall audits │
                              └─────────────────┘
```

### 4.2 Pin policy

| Rule | Detail |
|------|--------|
| **Single Lean version** | One `lean-toolchain` for the deploy monorepo path (today: **v4.32.0**) |
| **Mathlib tag lock** | `rev = "v4.32.0"` (or matching commit); bump only as a **version campaign** |
| **Physlib pin** | Git rev or tag in `lakefile.toml` **matching** Mathlib/Lean; record in manifest |
| **Optional targets** | Prefer `lake build QuantumInfo` over full Physlib when QP-only |
| **Bump procedure** | (1) branch, (2) bump toolchain + both deps, (3) `lake update`, (4) full build, (5) re-attest affected modules, (6) firewall, (7) commit hash for partners |
| **No floating `main`** | Never depend on unpinned Physlib/Mathlib HEAD in production |

**Compatibility note (2026-08-02):** Physlib upstream advertises Lean **v4.32.0** and Mathlib **v4.32.0** — same as Brockian. First harvest should **lock a commit SHA**, not only a version label, to freeze declaration sets.

### 4.3 Lake / dependency layout (recommended)

Phased introduction (does not require immediate monorepo merge):

| Phase | Layout | Rationale |
|-------|--------|-----------|
| **H0** | Mathlib only (status quo) | Stable Brockian core |
| **H1** | Optional Lake require `physlib` with **feature flag** / separate package `BrockianQI` | Isolate build cost |
| **H2** | Split packages: `brockian-core`, `brockian-qi` (depends on QuantumInfo), `brockian-gate1` | CI matrix; partners build only what they need |
| **H3** | Vendored **declaration allowlist** (re-export modules) | Import surface control; prevents accidental Alpha/QFT pull |

**Import hygiene:**

- Forbid `import Mathlib` in new harvest modules; use leaf modules.  
- Prefer `import QuantumInfo....` leaves over umbrella imports.  
- Run Physlib/Mathlib linters only on *our* code; do not re-lint entire upstream in CI every commit (cache).

### 4.4 Attestation & registration

Existing tools (do not reinvent):

| Tool | Role |
|------|------|
| `scripts/attest.py` | Module → AXLE check → `registry/attestations/<Module>.json` |
| `scripts/settle.py` | Certificate factory: prove/refute race → axioms → no-theater → certificate |
| `scripts/gen_registry.py` | **Derived** registers → `registry/theorems.json` |
| `scripts/no_theater_lint.py` | Degenerate / ex-falso / overtitle guard |
| `scripts/audit_dependency_firewall.py` | PROVED must not cite open CONDITIONAL as independent |
| `scripts/list_upstream_decls.py` | Inventory for Mathlib extract |
| `scripts/ingest_discover.py` | Discovery aid for intake |

**Harvest-specific attestation classes (proposed provenance tags):**

| Provenance | Meaning | May earn PROVED? |
|------------|---------|------------------|
| `brockian` | Proof body owned in `Brockian/` | Yes (standard triple gate) |
| `mathlib-import` | Used as dependency only | No separate PROVED row for upstream decl |
| `mathlib-wrapper` | Thin local theorem over Mathlib | Yes if wrapper is non-trivial and gates pass |
| `physlib-import` | Dependency only | No |
| `physlib-reattest` | Independent AXLE check of upstream statement at pin | **Yes only if** we record *source* and do not claim authorship; partner surfaces show “community theorem, independently re-verified” |
| `physlib-alpha` | Staging | Never PROVED on production surfaces |

**Axiom gate (unchanged):**

```
#print axioms ⊆ {propext, Classical.choice, Quot.sound}
no sorry / admit
no native_decide for PROVED
```

Physlib modules that introduce extra axioms or `sorry` must be **quarantined** even if they build with `-Dwarn.sorry=false` (Physlib lakefile uses relaxed sorry warn for some libs — **our** gate does not).

### 4.5 Register join checklist (per harvested module)

1. Pin SHA recorded in lakefile/manifest.  
2. `lake build <target>` green on CI + local.  
3. Declaration allowlist chosen (not whole tree).  
4. `attest.py` / `settle.py` for wrappers and re-attests.  
5. `gen_registry.py` → summary diff reviewed.  
6. `audit_dependency_firewall.py --fail-on-high`.  
7. `audit_registry_opens.py` / consistency scripts.  
8. Observatory / partner brief numbers only from this export.  
9. Provenance note: source repo + commit + declaration name.

### 4.6 CI matrix (target)

| Job | Command sketch | Purpose |
|-----|----------------|---------|
| core | `lake build Brockian` | Always |
| qi (optional) | `lake build BrockianQI` or QuantumInfo consumers | Nightly or label-gated |
| attest sample | AXLE on changed modules | PR gate |
| firewall | `audit_dependency_firewall.py --fail-on-high` | PR gate |
| registry fresh | `check_registry_fresh.py` | Release gate |

---

## 5. 30 / 60 / 90 day harvest milestones

Calendar relative to plan date **2026-08-02**. Aligns with strategy brief Phase D (scale harvest) and Phase C deploy demos.

### Day 0–30 — Map, pin, zero-bloat foundation

| # | Milestone | Exit criteria |
|---|-----------|---------------|
| M30.1 | **Inventory spreadsheet / YAML** of Mathlib areas used by Brockian + gaps from UPSTREAM-CANDIDATES | File under `docs/partner/` or `pipeline/catalog/` (ops may add later); declaration-level for top 50 deps |
| M30.2 | **Physlib pin experiment** — clone at SHA; `lake build QuantumInfo` on same Lean 4.32.0 | Build log archived; time/disk measured |
| M30.3 | **Crosswalk v0**: QI Entropy/Channels/States ↔ QuantumProof demo props | 5–15 candidate lemmas listed with IMPORT vs RE-ATTEST |
| M30.4 | **Crosswalk v0**: Physlib QM Unbounded/Spectral ↔ `Weyl*` | Table of overlaps / conflicts |
| M30.5 | **Import hygiene pilot** on 3 Brockian modules (focused Mathlib imports) | PR-ready patch list (implementation later) |
| M30.6 | **Provenance tag design** approved (schema fields for harvest sources) | Written into this plan §4.4; gen_registry extension sketched |
| M30.7 | **Partner demo pick**: exactly **one** entropy/DPI-style lemma + **one** finite modular/PQC-model lemma | Named statements; assumptions explicit |

**Non-milestones (explicitly not required by day 30):** full Physlib in monorepo; Mathlib PR merged; ESA closed.

### Day 31–60 — Thin integrate + first re-attests + Gate-1 audit

| # | Milestone | Exit criteria |
|---|-----------|---------------|
| M60.1 | Optional Lake package **or** sibling repo consuming **QuantumInfo only** at pinned SHA | Documented `lakefile` fragment; CI job green |
| M60.2 | **Re-attest** 3–10 QI theorems used by demo (AXLE @ lean-4.32.0) | Attestation JSON + provenance `physlib-reattest` |
| M60.3 | **Wrapper lemmas** for QP demo compiled in Brockian (or `QuantumProof` formal package) | Registry rows for wrappers only |
| M60.4 | Mathlib **gap audit refresh** vs UPSTREAM-CANDIDATES (IsSymmetric etc.) | Update note: still missing / landed upstream |
| M60.5 | Sieve cluster: list of **deletable re-proofs** if Mathlib already covers | Candidate deletions documented (no mass delete without build) |
| M60.6 | Gate-1: CONDITIONAL inventory synced with registry (weak regularity, Fourier ESA, Kato transfer) | Matches `REGISTRY` / provenance |
| M60.7 | Firewall green on harvest-touched registry export | `--fail-on-high` clean |

### Day 61–90 — Deploy surface + bidirectional discipline

| # | Milestone | Exit criteria |
|---|-----------|---------------|
| M90.1 | **IonQ/QP demo path**: job or hybrid mock → classical post-process → **registry-badged** lemma | Partner-visible artifact (badge + assumptions) |
| M90.2 | Second demo (PQC model or hybrid composition) or deepened entropy claim | Same honesty grammar |
| M90.3 | Mathlib upstream **one** PR opened *or* local extraction file ready (IsSymmetric / range API) | Links to MATHLIB-PR-BLUEPRINTS PR1–2 |
| M90.4 | Cycle/Fourier generalization plan (n not only 5) documented with Mathlib targets | Spec only or partial formalization |
| M90.5 | **Bloat budget**: document max allowed dependency weight for `brockian-qi` vs core | CI fails if full QFT tree pulled |
| M90.6 | Dual-env re-attest plan (AXLE + local lake) for harvest wrappers | Removes “AXLE-only asterisk” for partner demos |
| M90.7 | Strategy brief Phase D checklist complete | Mathlib map + Physlib substrate + pipeline catalog cards updated |

### Milestone dependency sketch

```
M30 inventory ──► M60 QI package ──► M90 IonQ demo
M30 pin build ──► M60 re-attest ──┘
M30 Gate-1 map ──► M60 CONDITIONAL sync ──► M90 Mathlib PR / extraction
M30 hygiene   ──► M60 delete-candidates ──► ongoing bloat control
```

---

## 6. Risks — version pins, bloat, axiom pollution

### 6.1 Version pins

| Risk | Severity | Mitigation |
|------|----------|------------|
| Mathlib/Physlib **skew** (different Lean tags) | High | Single toolchain; refuse dual Lean versions in one deploy artifact |
| Physlib moves faster than Brockian re-attest capacity | Medium | Pin SHA; quarterly bump campaigns; allowlist decls |
| Mathlib refactor renames (`LinearPMap` API churn) | Medium | Wrapper modules; import graph tests; bump branch early |
| AXLE env lag vs local pin | High for partners | Dual leg: local `lake build` + AXLE; never ship AXLE-only for harvest demos long-term |
| Cache / disk blowup on M4 16GB host | Medium | QuantumInfo-only builds; Nightly full; OrbStack discipline |

### 6.2 Bloat

| Risk | Severity | Mitigation |
|------|----------|------------|
| Importing full Physlib + Mathlib into every CI job | High | Package split; label-gated CI; allowlist re-exports |
| Re-proving Mathlib lemmas “for counts” | **Existential brand** | Registry provenance; no-theater; review checklist |
| Duplicate operator stacks (Brockian Weyl vs Physlib QM Unbounded) | Medium | Crosswalk; pick one public API; bridge lemmas |
| Paper/observatory inflated by harvest | High | Separate **harvested** vs **core** surfaces in UI; commit-scoped counts |
| PhyslibAlpha accidental dependency | High | Lakefile forbid; lint on import path |

**Budget guideline (operational):**

- **Core package:** Mathlib only; size discipline as today.  
- **QI package:** Mathlib + QuantumInfo (+ minimal Physlib QM if needed).  
- **Never:** String/QFT/Cosmology trees in QP production binary.

### 6.3 Axiom pollution

| Risk | Severity | Mitigation |
|------|----------|------------|
| Upstream `sorry` tolerated by Physlib flags | **Critical** | Our build must fail on sorry in *consumed* allowlist; do not inherit `-Dwarn.sorry=false` for production targets |
| Extra axioms beyond `{propext, Classical.choice, Quot.sound}` | Critical | Axiom gate on every PROVED / re-attest; quarantine offenders |
| `native_decide` / `ofReduceBool` sneaking into “PROVED” | High | Existing gate; extend to re-attests |
| Axiomatized entropy shortcuts (`QuantumInfo/Entropy/Axiomatized`) | High | Prefer non-axiomatized modules; if used, mark CONDITIONAL / literature rung |
| Silent classical assumptions in “security” lemmas | **Brand-destroying** | Named hypotheses; CONDITIONAL if open; partner copy lint |
| Firewall bypass via mixed modules | Medium | `audit_dependency_firewall.py`; split open vs closed files |

### 6.4 Process / partner risks

| Risk | Mitigation |
|------|------------|
| Partner reads “1477 + Mathlib” as one number | Always separate core vs harvested; cite commit |
| IonQ demo overclaims physical entropy | Badge text: model assumptions first |
| SAIR/distillation confuses harvest with original research | Provenance tags on every registry row |
| Dual stack maintenance burnout | Prefer IMPORT + thin wrap; upstream gaps to Mathlib PRs |

### 6.5 Risk register summary

| ID | Risk | Likelihood | Impact | Owner posture |
|----|------|------------|--------|---------------|
| R1 | Pin skew breaks builds | Med | High | Version campaign owner |
| R2 | Dependency bloat | High | Med | Package split |
| R3 | Axiom/sorry pollution | Med | Critical | Axiom gate + Alpha ban |
| R4 | Count inflation | Med | Critical | Provenance + UI |
| R5 | Operator-theory fork | Med | Med | Crosswalk + single public API |
| R6 | Overclaim on IonQ demo | Med | Critical | Honesty charter / firewall |

---

## 7. Worked examples (classification)

| Statement | Action | Rationale |
|-----------|--------|-----------|
| `ZMod` CRT equivalence | IMPORT | Mathlib |
| `admissibleResidues_crt_card` | Keep RE-PROVED (already) | Brockian packaging |
| `LinearPMap.IsSymmetric` (if absent upstream) | RE-PROVE locally; PR to Mathlib | Gap fill |
| von Neumann DPI lemma in QI | IMPORT + RE-ATTEST for demo | Partner diligence |
| Full free Laplacian ESA on L² | CONDITIONAL scaffold | Open Fourier/regularity inputs |
| PhyslibAlpha experimental channel | Quarantine | Review bar |
| “RH from BrockianSystem” | CONDITIONAL only | Never harvest into PROVED |

---

## 8. Success metrics (90-day)

| Metric | Target |
|--------|--------|
| Pinned Physlib SHA building QuantumInfo on Brockian toolchain | Yes |
| Partner demos with registry badges under named assumptions | ≥ 1 (stretch 2) |
| Re-attested upstream lemmas with provenance | ≥ 3 |
| New Mathlib-oriented extraction (PR or local extract file) | ≥ 1 spine item |
| Production PROVED count inflation from raw upstream import | **0** |
| Firewall high findings on release export | **0** |
| Documented allowlist (no Alpha, no full QFT) | Yes |

---

## 9. Immediate next actions (operators)

1. Freeze Physlib **commit SHA** compatible with Lean/Mathlib **v4.32.0**.  
2. Draft declaration allowlist for `QuantumInfo.Entropy` + `Channels` + `States`.  
3. Name the first QP formal target statement (entropy/DPI or hybrid model).  
4. Refresh Mathlib gap audit for `LinearPMap` symmetric/deficiency API.  
5. Extend provenance schema sketch for `physlib-reattest` (no registry inflation).  
6. Keep RH / Goldbach global / unbounded ESA off every harvest marketing surface.

---

## 10. References

| Resource | URL / path |
|----------|------------|
| Physlib repo | https://github.com/leanprover-community/physlib |
| Physlib site | https://physlib.io |
| Physlib origin (HepLean/PhysLean) | arXiv:2405.08863 |
| QI Stein formalization | arXiv:2510.08672 |
| Mathlib | https://github.com/leanprover-community/mathlib4 |
| Local upstream candidates | `docs/MATHLIB-UPSTREAM-CANDIDATES.md` |
| Local PR blueprints | `docs/MATHLIB-PR-BLUEPRINTS.md` |
| Strategy brief | `docs/partner/2026-08-02-verified-intelligence-strategy-brief.md` |
| Registry SSOT | `REGISTRY.md`, `registry/theorems.json` |

---

*End of harvest plan. Implementation requires separate engineering tickets; this document does not modify Lean sources, pins, or registry artifacts.*
