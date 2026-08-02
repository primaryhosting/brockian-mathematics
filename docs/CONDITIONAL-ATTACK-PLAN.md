# Conditional Attack Plan — dispatch to Grok / OpenAI(Codex) / Harmonic(Aristotle) / Axiom(AXLE)

Per-conditional strategy for the 18 open CONDITIONAL + 1 CONJECTURE (as of tip near 1289 PROVED).
**Honesty rule:** Group C items are open-problem-strength — no prover closes them; their workload is
*reduce/strengthen the schema*, never a fake "full proof." Every result is gated through AXLE (Axiom)
+ `#print axioms` + `no_theater_lint` + coherence before it counts. Full close of a Group A/B item →
its conditional(s) drop or move to DISCHARGED.

Tool roles:
- **Harmonic (Aristotle)** — strongest proof *generator* for hard classical Lean lemmas. Retrieval was
  flaky; recovered. Submit self-contained flattened targets in `aristotle/<name>/`.
- **Axiom (AXLE)** — the independent verifier AND our general-purpose swarm's self-verify leg. The
  retrievable workhorse: agents write a module, AXLE-verify, hand back for gated integration.
- **Grok / OpenAI (Codex)** — concurrent repo agents; assigned targets via this doc + AGENT-COORDINATION.md.

---

## Group A — DISCHARGEABLE CLASSICAL (real full-proof targets)

| # | Conditional | Discharge target | Strategy | Assigned |
|---|---|---|---|---|
| A1 | `DeficiencyODE::deficiencyRepresentsODE_of_weakRegularity` + `::schrodinger_essentiallySelfAdjoint_of_weakRegularity` | `WeakSolutionRegularity V` (1D elliptic regularity: weak L² soln of y″=(V−z)y has a twice-diff L² representative, continuous V) | Formalize 1D interior elliptic regularity via Mathlib ODE/`ContDiff`/distribution tools; the weak identity against Schwartz ⇒ classical soln | **Harmonic** (job `c400008b`, running, monitored) + **Codex** (Weyl lane) |
| A2 | `SchrodingerMinimal::schrodinger_essentiallySelfAdjoint_of_ode` | same ODE-regularity family as A1 | folds into A1's `WeakSolutionRegularity`; then instantiate the concrete minimal T | folds into A1 |
| A3 | `FreeLaplacian2::freeLaplacian_essentiallySelfAdjoint_of_fourier` | free −Δ is unitarily mult-by-ξ² via the L² Fourier–Plancherel transform | Use Mathlib `fourierIntegral`/`Real.fourierIntegral`/Plancherel L² isometry to conjugate −Δ to ξ² multiplication (self-adjoint) | **Harmonic** (submit Plancherel target) + **AXLE swarm** (race, retrievable) |
| A4 | `KatoUnbounded::essentiallySelfAdjoint_perturb` | Kato–Rellich: T ESA + V relatively-T-bounded (bound <1) ⇒ T+V ESA | Formalize relative-boundedness + the Kato–Rellich range-density argument | **Codex** (Weyl lane) |

## Group B — REDUCE-ONLY ANALYTIC (BV/HL uncloseable at Mathlib 4.32)

| # | Conditional | Attackable sub-target | Strategy | Assigned |
|---|---|---|---|---|
| B1 | `EquidistributionBVReduction::{configCount_density_of_BV, equidistribution_of_BV_uniform, configCount_over_main_tendsto, total_over_main_tendsto}` | the **uniformity symmetry** `sing a = sing b` on admissible classes (the extra input the reduction exposed) | Prove the singular-series constant is class-independent from the reflection/affine symmetry of admissible residues; BV/HL stays the cited literature hypothesis | **AXLE swarm** |
| B2 | `Equidistribution::{equidistribution_of_asymptotic, equidistribution_of_asymptotic_exists}` | superseded by B1's BV path | if B1's uniform density lands, mark these `discharged_by` the BV-uniform result; else keep as the honest open schema | **Claude** (bookkeeping) |

## Group C — FRONTIER (open-problem-strength; REDUCE/STRENGTHEN ONLY, never fake)

| # | Conditional / Conjecture | Why uncloseable | Honest workload | Assigned |
|---|---|---|---|---|
| C1 | `RiemannScaffold::RH_of_BrockianSystem` | inhabiting `BrockianSystem` = Hilbert–Pólya (RH) | strengthen the ξ-bridge (functional eq. done); sharpen the Hilbert–Pólya criterion to the minimal named hypothesis | Grok/Codex — reduce only |
| C2 | `GoldbachSchema::{goldbach_from_spectral_model, goldbach_beyond_of_model}` | instantiating `SpectralModel` = Goldbach | prove additional *local* SpectralModel structure; keep global transfer open | Grok — reduce only |
| C3 | `GoldbachComb::GoldbachCovarianceTransfer` (CONJECTURE) | the global Goldbach transfer | keep as the honest named conjecture; add the circle-method major-arc main term as a separate CONDITIONAL | Grok — reduce only |
| C4 | `WeylLawTarget::{counting_diverges_of_candidate, _of_discrete_and_WeylLawMatch, _of_discrete_and_rvm, _of_exists}` | requires the actual RH operator + its spectrum | keep as honest schemas of what an RH operator must satisfy; wire to a concrete confining candidate if one is constructed | Grok — reduce only |

---

## Dispatch status
- Harmonic: `c400008b` weak-regularity (A1) RUNNING + monitored; Plancherel (A3) target to submit.
- AXLE swarm: A3 (Plancherel race) + B1 (uniformity symmetry) launched.
- Codex: A1/A2/A4 (Weyl lane) via AGENT-COORDINATION.md.
- Grok: C1–C4 reduce-only via AGENT-COORDINATION.md.
