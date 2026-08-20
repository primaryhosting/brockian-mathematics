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

lemma integral_partialSum_sq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x ↦ x ^ 2) μ) (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1)
    (m : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range m, ω i) ^ 2 ∂(iidLaw μ) = m := by
  have hmem : ∀ i, MemLp (fun ω : ℕ → ℝ ↦ ω i) 2 (iidLaw μ) := memLp_eval μ hint
  have hzero : ∫ ω : ℕ → ℝ, (∑ i ∈ Finset.range m, ω i) ∂(iidLaw μ) = 0 := by
    rw [integral_finset_sum _ (fun i _ ↦ ((hmem i).integrable one_le_two))]
    simp [integral_eval μ hmean]
  have hvarsum : Var[fun ω : ℕ → ℝ ↦ ∑ i ∈ Finset.range m, ω i; iidLaw μ] = m := by
    have hfun : (fun ω : ℕ → ℝ ↦ ∑ i ∈ Finset.range m, ω i)
        = ∑ i ∈ Finset.range m, (fun ω : ℕ → ℝ ↦ ω i) := by
      ext ω; simp
    rw [hfun, IndepFun.variance_sum (fun i _ ↦ hmem i)
      (fun i _ j _ hij ↦ indepFun_eval μ hij)]
    simp [variance_eval μ hmean hvar]
  rw [← hvarsum, variance_of_integral_eq_zero
    ((memLp_partialSum μ hint m).aestronglyMeasurable.aemeasurable) hzero]

/-! ### The second moment of the rescaled walk -/

