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

theorem logZDensity_zero (L : ℕ) (hL : 0 < L) : logZDensity L 0 = Real.log 2 := by
  have hL' : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hL.ne'
  rw [logZDensity, isingZ_zero, Real.log_pow]
  field_simp
  push_cast
  ring

/-! ### Rigorous bounds on the free energy, valid in every finite volume -/

