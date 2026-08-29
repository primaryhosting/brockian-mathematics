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

theorem bondSum_allUp (L : ℕ) : bondSum (fun _ => true : Config L) = 2 * (L : ℝ) ^ 2 := by
  simp [bondSum, spin, Finset.sum_const]; ring

