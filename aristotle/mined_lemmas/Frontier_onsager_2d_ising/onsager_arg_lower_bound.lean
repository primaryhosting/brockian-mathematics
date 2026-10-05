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

theorem onsager_arg_lower_bound (K θ φ : ℝ) (hK : 0 ≤ K) :
    (Real.sinh (2 * K) - 1) ^ 2 ≤
      Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos θ + Real.cos φ) := by
  have h1 : Real.cosh (2 * K) ^ 2 = 1 + Real.sinh (2 * K) ^ 2 := by
    have := Real.cosh_sq_sub_sinh_sq (2 * K); nlinarith
  have hs : 0 ≤ Real.sinh (2 * K) := by
    rw [← Real.sinh_zero]; exact Real.sinh_le_sinh.2 (by linarith)
  nlinarith [Real.cos_le_one θ, Real.cos_le_one φ]

/-- Off the critical coupling the argument of Onsager's logarithm is strictly positive
for all `θ, φ`; the bound degenerates exactly at `K = K_c` (and there only at `θ = φ = 0`). -/
