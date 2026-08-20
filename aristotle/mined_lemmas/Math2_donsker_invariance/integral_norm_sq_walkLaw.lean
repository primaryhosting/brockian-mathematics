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

lemma integral_norm_sq_walkLaw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x ↦ x ^ 2) μ) (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1)
    (n : ℕ) :
    ∫ x, ‖x‖ ^ 2 ∂(walkLaw μ t k n) = ∑ j : Fin k, (stepCount t n j : ℝ) / n := by
  rw [walkLaw, integral_map (measurable_walkVec t k n).aemeasurable (by fun_prop)]
  have hfun : (fun ω : ℕ → ℝ ↦ ‖walkVec t k n ω‖ ^ 2)
      = fun ω ↦ ∑ j : Fin k,
        ((∑ i ∈ Finset.range (stepCount t n j), ω i) / Real.sqrt n) ^ 2 := by
    ext ω
    rw [norm_sq_euclidean]
    rfl
  rw [hfun]
  have hint' : ∀ j : Fin k, Integrable
      (fun ω : ℕ → ℝ ↦ ((∑ i ∈ Finset.range (stepCount t n j), ω i) / Real.sqrt n) ^ 2)
      (iidLaw μ) := by
    intro j
    have hsq : Integrable (fun ω : ℕ → ℝ ↦ (∑ i ∈ Finset.range (stepCount t n j), ω i) ^ 2)
        (iidLaw μ) := by
      rw [← memLp_two_iff_integrable_sq (memLp_partialSum μ hint _).aestronglyMeasurable]
      exact memLp_partialSum μ hint _
    refine (hsq.div_const ((Real.sqrt n) ^ 2)).congr ?_
    filter_upwards with ω
    rw [div_pow]
  rw [integral_finset_sum _ fun j _ ↦ hint' j]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hdiv : ∀ ω : ℕ → ℝ,
      ((∑ i ∈ Finset.range (stepCount t n j), ω i) / Real.sqrt n) ^ 2
        = (∑ i ∈ Finset.range (stepCount t n j), ω i) ^ 2 / n := by
    intro ω
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  simp only [hdiv]
  rw [integral_div, integral_partialSum_sq μ hint hmean hvar]

/-- The second moment of the rescaled walk vector is bounded uniformly in `n`. -/
