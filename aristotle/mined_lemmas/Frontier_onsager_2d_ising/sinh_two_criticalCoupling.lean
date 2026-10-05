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

theorem sinh_two_criticalCoupling : Real.sinh (2 * criticalCoupling) = 1 := by
  have h2 : (0:ℝ) < 1 + Real.sqrt 2 := by positivity
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [Real.sinh_eq,
    show 2 * criticalCoupling = Real.log (1 + Real.sqrt 2) by unfold criticalCoupling; ring,
    Real.exp_log h2, Real.exp_neg, Real.exp_log h2]
  field_simp
  nlinarith [Real.sqrt_nonneg 2]

/-- The argument of Onsager's logarithm is bounded below by `(sinh 2K - 1)²`, hence is
nonnegative for all `K ≥ 0`. -/
