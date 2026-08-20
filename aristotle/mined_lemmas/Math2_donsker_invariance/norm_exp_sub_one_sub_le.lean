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

lemma norm_exp_sub_one_sub_le (a : ℝ) :
    ‖Complex.exp (-((a : ℂ) ^ 2) / 2) - (1 - (a : ℂ) ^ 2 / 2)‖ ≤ a ^ 4 := by
  have hcast : Complex.exp (-((a : ℂ) ^ 2) / 2) - (1 - (a : ℂ) ^ 2 / 2)
      = ((Real.exp (-(a ^ 2) / 2) - (1 - a ^ 2 / 2) : ℝ) : ℂ) := by
    have h : ((-(a ^ 2) / 2 : ℝ) : ℂ) = -((a : ℂ) ^ 2) / 2 := by push_cast; ring
    rw [← h, ← Complex.ofReal_exp]
    push_cast
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  set y := a ^ 2 / 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have hexp : Real.exp (-(a ^ 2) / 2) = Real.exp (-y) := by rw [hy]; ring_nf
  rw [hexp]
  rcases le_or_gt y 1 with h | h
  · have := Real.abs_exp_sub_one_sub_id_le (x := -y) (by rw [abs_neg, abs_of_nonneg hy0]; exact h)
    have habs : |Real.exp (-y) - (1 - y)| = |Real.exp (-y) - 1 - -y| := by ring_nf
    rw [habs]
    refine this.trans ?_
    have : y ^ 2 = a ^ 4 / 4 := by rw [hy]; ring
    nlinarith [pow_nonneg (sq_nonneg a) 2, sq_nonneg (a ^ 2)]
  · have h1 : 0 < Real.exp (-y) := Real.exp_pos _
    have h2 : Real.exp (-y) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have h3 : |Real.exp (-y) - (1 - y)| ≤ y := by
      rw [abs_le]
      constructor <;> linarith
    have h4 : y ≤ y ^ 2 := by nlinarith
    have h5 : y ^ 2 = a ^ 4 / 4 := by rw [hy]; ring
    nlinarith [sq_nonneg (a ^ 2)]

/-! ### The Taylor error of a characteristic function -/

/-- The error term in the second order Taylor expansion of a characteristic function. -/
