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

lemma integrable_taylorErr_integrand (μ : Measure ℝ) (hint : Integrable (fun x ↦ x ^ 2) μ)
    {u : ℝ} (hu : 0 ≤ u) : Integrable (fun x : ℝ ↦ min (u * |x| ^ 3) (4 * x ^ 2)) μ := by
  have hb : Integrable (fun x : ℝ ↦ 4 * x ^ 2) μ := hint.const_mul 4
  refine Integrable.mono hb (measurable_taylorErr_integrand u).aestronglyMeasurable ?_
  filter_upwards with x
  have h0 : 0 ≤ min (u * |x| ^ 3) (4 * x ^ 2) :=
    le_min (mul_nonneg hu (by positivity)) (by positivity)
  have h1 : min (u * |x| ^ 3) (4 * x ^ 2) ≤ 4 * x ^ 2 := min_le_right _ _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * x ^ 2)]
  exact h1

