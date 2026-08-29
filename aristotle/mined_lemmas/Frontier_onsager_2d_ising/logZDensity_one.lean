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

theorem logZDensity_one (K : ℝ) : logZDensity 1 K = Real.log 2 + 2 * K := by
  rw [logZDensity, isingZ_one]
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  norm_num

/-- The exact free-energy density at infinite temperature, for every finite volume. -/
