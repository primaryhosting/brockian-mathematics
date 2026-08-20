/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.Donsker.Defs
import RequestProject.Donsker.CharFun
import RequestProject.Donsker.CLT
import RequestProject.Donsker.Tight
import RequestProject.Donsker.Levy

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace

namespace Math2

/-- **Donsker's invariance principle** (convergence of the finite-dimensional distributions).

Let `μ` be the law of a centered step with unit variance, let `S_m` be the associated random walk
with i.i.d. steps (the steps being the coordinates of `ℕ → ℝ` under the product measure
`Math2.iidLaw μ`), and let `W_n(u) = S_{⌊n u⌋} / √n` be the rescaled walk.

Then, for any finite set of times `t 0 ≤ t 1 ≤ … ≤ t (k-1)`, the law `Math2.walkLaw μ t k n` of
the random vector `(W_n(t 0), …, W_n(t (k-1)))` converges weakly, as `n → ∞`, to the law
`Math2.bmLaw t k` of `(B_{t 0}, …, B_{t (k-1)})`, where `B` is a Brownian motion.  Weak
convergence is expressed as convergence of the integrals of all bounded continuous functions.

The limit does not depend on the step distribution `μ` (only on its mean and variance): this is
the invariance in Donsker's invariance principle.  That `Math2.bmLaw t k` really is the
finite-dimensional distribution of Brownian motion is the content of
`Math2.charFun_bmLaw_eq`: it is the centered Gaussian law with covariance
`min (t i) (t j)`. -/

theorem tendsto_probabilityMeasure_of_tendsto_charFun
    (P : ℕ → ProbabilityMeasure E) (Q : ProbabilityMeasure E)
    (htight : IsTightMeasureSet {((P n : Measure E)) | n : ℕ})
    (hchar : ∀ s, Tendsto (fun n ↦ charFun (P n : Measure E) s) atTop
      (𝓝 (charFun (Q : Measure E) s))) :
    Tendsto P atTop (𝓝 Q) := by
  have hcompact : IsCompact (closure (Set.range P)) := by
    refine isCompact_closure_of_isTightMeasureSet ?_
    convert htight using 2
    ext ν
    constructor
    · rintro ⟨R, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨P n, ⟨n, rfl⟩, rfl⟩
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  have hmem : ∀ n, P (ns n) ∈ closure (Set.range P) := fun n ↦ subset_closure ⟨ns n, rfl⟩
  obtain ⟨Q', -, phi, hphi, hlim⟩ := hcompact.tendsto_subseq hmem
  have hlim' : Tendsto (fun n ↦ P (ns (phi n))) atTop (𝓝 Q') := hlim
  have hQeq : Q' = Q := by
    have hcf : ∀ s : E, charFun (Q' : Measure E) s = charFun (Q : Measure E) s := by
      intro s
      have h1 : Tendsto (fun n ↦ charFun (P (ns (phi n)) : Measure E) s) atTop
          (𝓝 (charFun (Q' : Measure E) s)) := by
        have h := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hlim'
          (charFunBCF s)
        simpa only [integral_charFunBCF] using h
      have h2 : Tendsto (fun n ↦ charFun (P (ns (phi n)) : Measure E) s) atTop
          (𝓝 (charFun (Q : Measure E) s)) := (hchar s).comp (hns.comp hphi.tendsto_atTop)
      exact tendsto_nhds_unique h1 h2
    apply ProbabilityMeasure.toMeasure_injective
    exact Measure.ext_of_charFun (funext hcf)
  exact ⟨phi, hQeq ▸ hlim'⟩

/-- Lévy's continuity theorem (tight version), stated for integrals of bounded continuous
functions. -/
