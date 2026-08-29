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

theorem isingZ_pos (L : ℕ) (K : ℝ) : 0 < isingZ L K := by
  apply Finset.sum_pos (fun σ _ => Real.exp_pos _)
  exact Finset.univ_nonempty

/-- At infinite temperature (`K = 0`) the partition function counts all `2^{L²}`
configurations. -/
