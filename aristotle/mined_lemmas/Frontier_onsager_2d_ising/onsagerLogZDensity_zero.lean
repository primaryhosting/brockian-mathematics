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

theorem onsagerLogZDensity_zero : onsagerLogZDensity 0 = Real.log 2 := by
  simp [onsagerLogZDensity, onsagerIntegrand_zero]

/-- `sinh (2 K_c) = 1`: Onsager's critical coupling. -/
