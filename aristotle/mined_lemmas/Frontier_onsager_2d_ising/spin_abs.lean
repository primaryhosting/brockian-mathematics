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

theorem spin_abs {L : ℕ} (σ : Config L) (x : Fin L × Fin L) : |spin σ x| = 1 := by
  unfold spin; split <;> norm_num

/-- Every configuration has bond energy at most that of the ground state. -/
