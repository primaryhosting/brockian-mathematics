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

lemma tendsto_taylorErr (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x ↦ x ^ 2) μ) (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hu0 : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n ↦ taylorErr μ (u n)) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n x ↦ min (u n * |x| ^ 3) (4 * x ^ 2)) (f := fun _ : ℝ ↦ (0 : ℝ))
    (bound := fun x ↦ 4 * x ^ 2)
    (fun n ↦ (measurable_taylorErr_integrand (u n)).aestronglyMeasurable)
    (hint.const_mul 4)
    (fun n ↦ by
      filter_upwards with x
      have h0 : 0 ≤ min (u n * |x| ^ 3) (4 * x ^ 2) :=
        le_min (mul_nonneg (hu n) (by positivity)) (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact min_le_right _ _)
    (by
      filter_upwards with x
      have hcube : Tendsto (fun n ↦ u n * |x| ^ 3) atTop (𝓝 0) := by
        simpa using hu0.mul_const (|x| ^ 3)
      refine squeeze_zero
        (fun n ↦ le_min (mul_nonneg (hu n) (by positivity)) (by positivity)) ?_ hcube
      exact fun n ↦ min_le_left _ _)
  simpa [taylorErr] using h

/-- Second order expansion of the characteristic function of a centered measure with unit
variance. -/
