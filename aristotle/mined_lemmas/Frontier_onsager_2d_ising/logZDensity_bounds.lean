import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Frontier

/-! ## The finite-volume 2D Ising model on an `L × L` torus -/

/-- Shift a periodic (torus) index by one site. -/

theorem logZDensity_bounds (L : ℕ) (K : ℝ) (hL : 0 < L) (hK : 0 ≤ K) :
    2 * K ≤ logZDensity L K ∧ logZDensity L K ≤ Real.log 2 + 2 * K := by
  have hL2 : (0:ℝ) < (L : ℝ) ^ 2 := by positivity
  have hZ : 0 < isingZ L K := isingZ_pos L K
  constructor
  · have h := Real.log_le_log (Real.exp_pos _) (isingZ_ge_ground L K)
    rw [Real.log_exp] at h
    rw [logZDensity, one_div, inv_mul_eq_div, le_div_iff₀ hL2]
    linarith
  · have h := Real.log_le_log hZ (isingZ_le L K hK)
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp] at h
    have hcast : ((L * L : ℕ) : ℝ) = (L : ℝ) ^ 2 := by push_cast; ring
    rw [hcast] at h
    rw [logZDensity, one_div, inv_mul_eq_div, div_le_iff₀ hL2]
    nlinarith [h]

/-! ## Onsager's expression: exact evaluation at `K = 0`, positivity, criticality -/

