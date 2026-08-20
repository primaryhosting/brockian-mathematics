import Mathlib

namespace Brockian.MsGaussSum

open Finset Complex

/-- The summand `exp (2πi k²/p)` is the value of the standard additive character at `k²`. -/

theorem gauss_sum_abs_sq (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    ‖∑ k : ZMod p,
      Complex.exp (2 * Real.pi * Complex.I * ((k.val : ℂ) ^ 2) / (p : ℂ))‖ ^ 2 = (p : ℝ) := by
  -- First, rewrite the sum using exp_eq_stdAddChar
  have h_sum_eq : ∑ k : ZMod p, Complex.exp (2 * Real.pi * Complex.I * ((k.val : ℂ) ^ 2) / (p : ℂ)) =
      ∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ) := by
    apply Finset.sum_congr rfl
    intro k _
    exact exp_eq_stdAddChar p k
  -- Rewrite the goal using h_sum_eq
  rw [h_sum_eq]
  -- Use the fact that ‖z‖² = z * conj(z) for complex numbers
  have h_norm_sq : ((‖∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      (∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ)) * (starRingEnd ℂ) (∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ)) := by
    rw [Complex.sq_norm, mul_comm]
    exact mod_cast Complex.normSq_eq_conj_mul_self
  have h_cast : ((‖∑ k : ZMod p, (ZMod.stdAddChar (k ^ 2) : ℂ)‖ ^ 2 : ℝ) : ℂ) = (p : ℂ) := by
    rw [h_norm_sq, gauss_sum_mul_conj p hp]
  exact mod_cast h_cast

end Brockian.MsGaussSum

