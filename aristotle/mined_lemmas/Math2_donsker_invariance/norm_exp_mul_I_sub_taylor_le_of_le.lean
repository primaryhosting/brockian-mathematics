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

lemma norm_exp_mul_I_sub_taylor_le_of_le (r : ℝ) (h : |r| ≤ 2) :
    ‖Complex.exp ((r : ℂ) * I) - (1 + (r : ℂ) * I - (r : ℂ) ^ 2 / 2)‖ ≤ |r| ^ 3 := by
  have hx : ‖((r : ℂ) * I)‖ = |r| := by simp
  have hI : ((r : ℂ) * I) ^ 2 = -(r : ℂ) ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
  have hsum : ∑ m ∈ Finset.range 3, ((r : ℂ) * I) ^ m / (m.factorial : ℂ)
      = 1 + (r : ℂ) * I - (r : ℂ) ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    push_cast
    rw [hI]
    ring
  have hb := Complex.exp_bound' (x := (r : ℂ) * I) (n := 3)
    (by rw [hx]; push_cast; linarith [abs_nonneg r])
  rw [hx, hsum] at hb
  refine hb.trans ?_
  have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6]
  nlinarith [pow_nonneg (abs_nonneg r) 3]

/-- Third order Taylor estimate for `exp (i r)`, with a quadratic bound for large `r`. -/
