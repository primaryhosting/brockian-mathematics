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

theorem bondSum_le {L : ℕ} (σ : Config L) : bondSum σ ≤ 2 * (L : ℝ) ^ 2 := by
  have h : ∀ x : Fin L × Fin L,
      (spin σ x * spin σ (shiftIdx x.1, x.2) + spin σ x * spin σ (x.1, shiftIdx x.2)) ≤ 2 := by
    intro x
    have h1 := abs_le.1 (le_of_eq (by rw [abs_mul, spin_abs, spin_abs]; norm_num :
      |spin σ x * spin σ (shiftIdx x.1, x.2)| = 1))
    have h2 := abs_le.1 (le_of_eq (by rw [abs_mul, spin_abs, spin_abs]; norm_num :
      |spin σ x * spin σ (x.1, shiftIdx x.2)| = 1))
    linarith [h1.2, h2.2]
  calc bondSum σ ≤ ∑ _x : Fin L × Fin L, (2 : ℝ) := Finset.sum_le_sum (fun x _ => h x)
    _ = 2 * (L : ℝ) ^ 2 := by simp [Finset.sum_const]; ring

/-- The all-up (ground state) configuration saturates the bound. -/
