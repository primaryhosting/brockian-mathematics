# Lean + Physics Repo Harvest — Concrete Inspection List

**Date:** 2026-08-02  
**Audience:** Claude / Codex / Grok multi-agent fleet + partners  
**Related:** `docs/partner/mathlib-physlean-harvest-plan.md`,  
`docs/superpowers/specs/2026-08-02-mathlib-physlean-harvest-design.md`,  
Claude harvest infra @ `e455a31` (`scripts/harvest/`, `torus/`, `export_public_registry.py`)

---

## 0. Principle

| Do | Don't |
|----|--------|
| Index / re-attest / depend on community libs | Inflate Brockian PROVED with “we indexed Mathlib” |
| Prefer **same Lean pin** (4.32.0) | Silent pin skew |
| Split counts by source: `brockian` / `mathlib` / `physlean` | Merge headline counts |
| Use `scripts/harvest/` + sanitized `torus/` export | Hand-paint badges on torus |

---

## 1. Priority repos

| Pri | Repo | Pin | Primary Brockian use |
|-----|------|-----|----------------------|
| **P0** | [mathlib4](https://github.com/leanprover-community/mathlib4) | match lake | Gate-1 operators, Fourier, NT |
| **P0** | [physlib](https://github.com/leanprover-community/physlib) | **v4.32.0** | QM models, QuantumInfo, IonQ surface |
| **P1** | [teorth/equational_theories](https://github.com/teorth/equational_theories) | check | SAIR Stage 1–2 |
| **P1** | [teorth/pfr](https://github.com/teorth/pfr) | check | Additive / entropy style |
| **P2** | AxiomMath NT formalizations | varies | Analytic NT culture |
| **P3** | Random RH Lean scaffolds | n/a | Read-only; firewall |

---

## 2. Physlib — first 5 decls / files per folder

Clone: `git clone https://github.com/leanprover-community/physlib.git`  
Build (selective): `lake build QuantumInfo` or `lake build Physlib`.

### 2.1 `Physlib/QuantumMechanics/FreeParticle/`

| # | Inspect | Why for Brockian |
|---|---------|------------------|
| 1 | `FreeParticle` structure (`Basic.lean`) | Physics packaging of free system |
| 2 | `FreeParticle.HS` | Hilbert space alias (`SpaceDHilbertSpace`) |
| 3 | `FreeParticle.hamiltonian` | `p²/(2m)` as `LinearPMap` — compare to `freeSchrodingerPMap` |
| 4 | `momentumSqOperator` (via `Operators.Momentum`) | Free kinetic building block |
| 5 | `hamiltonian_essentially_self_adjoint` | **Currently `informal_lemma`** — not a closed Lean proof; do not treat as PROVED |

**Gate-1 note:** Physlib free particle is a **model + informal ESA claim**, not a drop-in discharge of Brockian free-Δ Plancherel.

### 2.2 `Physlib/QuantumMechanics/Operators/`

| # | Inspect | Why |
|---|---------|-----|
| 1 | `Momentum.lean` | Momentum operator formalization |
| 2 | `Position.lean` | Multiplication / position |
| 3 | `Unbounded.lean` | Unbounded operator interface |
| 4 | `SpectralTheory/` | Spectrum language for demos |
| 5 | `Uncertainty.lean` | Finite/standard QM lemmas |

### 2.3 `Physlib/QuantumMechanics/HilbertSpaces/`

| # | Inspect | Why |
|---|---------|-----|
| 1 | `OneDimension/` | 1D L2 packaging vs Brockian `H2` |
| 2 | `SpaceD/` | d-dimensional free particle HS |
| 3 | `FiniteTarget` | Finite-dim toy systems (IonQ demos) |
| 4–5 | any `Basic` modules under those dirs | Naming + documentation style |

### 2.4 `Physlib/QuantumMechanics/` models

| # | Folder / file | Why |
|---|---------------|-----|
| 1 | `HarmonicOscillator/` | Solved ESA/spectrum narrative |
| 2 | `InfiniteSquareWell/` | 1D boundary-value model |
| 3 | `Hydrogen/` | 3D spectral model |
| 4 | `QuantumSystem/` | Generic quantum system interface |
| 5 | `SpaceDQuantumSystem.lean` | Space-dimension system glue |

### 2.5 `QuantumInfo/Entropy/` (IonQ / QuantumProof)

| # | File | Why |
|---|------|-----|
| 1 | `VonNeumann.lean` | vN entropy formalization |
| 2 | `Relative.lean` | Relative entropy (large; Stein’s lemma stack) |
| 3 | `DPI.lean` | Data processing inequality |
| 4 | `SSA.lean` | Strong subadditivity |
| 5 | `Axiomatized/` | Explicit axiomatic layer — **label LITERATURE/axiomatic, never merge into PROVED** |

**Papers:** arXiv [2405.08863](https://arxiv.org/abs/2405.08863) (HepLean), [2510.08672](https://arxiv.org/abs/2510.08672) (Stein’s lemma).

### 2.6 `QuantumInfo/States/` + `Channels/`

| # | Inspect | Why |
|---|---------|-----|
| 1 | `States/Pure`, `States/Mixed` | Density matrices |
| 2 | `States/Ensemble.lean` | Ensembles |
| 3 | `States/Entanglement.lean` | Entanglement measures |
| 4 | `Channels/*` (top modules) | CPTP maps |
| 5 | `ForMathlib/` | Upstream candidates |

---

## 3. Mathlib — first 5 modules for Gate-1 / NT

| # | Module path (concept) | Brockian consumer |
|---|----------------------|-------------------|
| 1 | `Mathlib.Analysis.InnerProductSpace.LinearPMap` | `WeylOperator` base |
| 2 | `…InnerProductSpace.Symmetric` / `Spectrum` / `Adjoint` | Real spectrum, resolvent |
| 3 | `…InnerProductSpace.Laplacian` | Free Laplacian |
| 4 | Fourier / Plancherel / `Lp` (on pin) | Free ESA stretch (Claude A3) |
| 5 | `NumberTheory` + `ZMod` + partitions | Sieve / Franklin already partially used |

**Upstream out (Brockian → Mathlib):** see `docs/MATHLIB-UPSTREAM-CANDIDATES.md`  
(`IsSymmetric`, non-real resolvent inequality).

---

## 4. SAIR / equational

| # | Source | Action |
|---|--------|--------|
| 1 | [teorth/equational_theories](https://github.com/teorth/equational_theories) | Offline implication set for cheatsheet scoring |
| 2 | Lean proofs/counterexamples in ETP | Stage-2 certificate format |
| 3 | `scripts/refute.py` | Emit finite countermodels |
| 4 | `scripts/settle.py --refute` | AXLE-verify REFUTED |
| 5 | `pipeline/distill/cheatsheets/etp_v1.txt` | ≤10KB Stage-1 artifact |

---

## 5. Other Lean NT (selective)

| Repo | Use | Avoid |
|------|-----|-------|
| AxiomMath `ramanujan-tau-misses-primes`, `partial-regularity` | Style / analytic NT | Claiming as Brockian |
| `bounded_gaps` Polymath8b scaffold | Vocabulary | Fake Maynard/Zhang |
| `riemann-resolvent-programme` et al. | Competitor RH scaffolds | Any PROVED merge |

---

## 6. How this plugs into Claude’s harvest infra

Claude shipped (@ `e455a31`):

```
scripts/harvest/ExtractEnv.lean + run_extract.py   # H1 NDJSON extract
scripts/harvest/schema.sql + ingest.py + search_api.py  # H2 store
scripts/export_public_registry.py                  # H3 sanitized export
torus/{VerifiedClaim.tsx, useVerified.ts, …}       # public badges
```

**Grok deploy/run (per board handoff — do not rebuild):**

```bash
# 1) Extract (prefer off-Mac-Mini / worktree with Mathlib+Physlib)
# lake env lean --run scripts/harvest/ExtractEnv.lean …  → out.ndjson

# 2) Ingest with source facets
python3 scripts/harvest/ingest.py …

# 3) Sanitized public registry
python3 scripts/export_public_registry.py
# → torus/public/verified-registry.json

# 4) Lovable: copy torus components + public JSON (torus/README.md)
```

Honesty: **never merge** `brockian` AXLE counts with indexed Mathlib/Physlib counts in UI.

---

## 7. Suggested inspection order (one afternoon)

1. Physlib `FreeParticle.Basic` vs Brockian `WeylSchrodingerGate1Final.freeSchrodingerPMap` (compare, don’t copy).  
2. Physlib `Operators.Momentum` + `Unbounded`.  
3. QuantumInfo `Entropy.VonNeumann` + `DPI` (IonQ one-pager language).  
4. Mathlib `LinearPMap` + `Spectrum` on current pin.  
5. ETP sample implications for `refute.py`.  
6. Run exporter on current Brockian registry; spot-check `VerifiedClaim` BLOCKED path for a fake RH name.

---

## 8. Pipeline card

Tracked as problem card: **`math-physlean-import`**  
(`pipeline/catalog/math/math-physlean-import.json`)

---

*Regenerate partner freeze with commit hash after harvest runs land.*
