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

lemma norm_exp_mul_I_sub_taylor_le (r : ℝ) :
    ‖Complex.exp ((r : ℂ) * I) - (1 + (r : ℂ) * I - (r : ℂ) ^ 2 / 2)‖
      ≤ min (|r| ^ 3) (4 * r ^ 2) := by
  have hnorm : ‖Complex.exp ((r : ℂ) * I)‖ = 1 := by simp [Complex.norm_exp_ofReal_mul_I]
  have hsq : |r| ^ 2 = r ^ 2 := sq_abs r
  have htriv : ‖Complex.exp ((r : ℂ) * I) - (1 + (r : ℂ) * I - (r : ℂ) ^ 2 / 2)‖
      ≤ 1 + (1 + |r| + r ^ 2 / 2) := by
    refine (norm_sub_le _ _).trans ?_
    rw [hnorm]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans ?_) ?_
    · simp
    · rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      simp
  rcases le_or_gt (|r|) 2 with hle | hgt
  · refine le_min (norm_exp_mul_I_sub_taylor_le_of_le r hle)
      ((norm_exp_mul_I_sub_taylor_le_of_le r hle).trans ?_)
    nlinarith [abs_nonneg r]
  · exact le_min (htriv.trans (by nlinarith [abs_nonneg r]))
      (htriv.trans (by nlinarith [abs_nonneg r]))

/-- Comparison of `exp (-a²/2)` with its first order expansion. -/
