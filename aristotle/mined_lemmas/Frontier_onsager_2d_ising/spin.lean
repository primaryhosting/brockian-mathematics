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

def spin {L : ℕ} (σ : Config L) (x : Fin L × Fin L) : ℝ := if σ x then 1 else -1

/-- `∑_{⟨x,y⟩} σ_x σ_y`, the sum over all nearest-neighbour bonds of the torus
(each site contributes its right and its upward bond). -/
