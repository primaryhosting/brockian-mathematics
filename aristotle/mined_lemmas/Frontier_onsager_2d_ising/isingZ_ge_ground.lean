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

theorem isingZ_ge_ground (L : ℕ) (K : ℝ) : Real.exp (2 * K * (L : ℝ) ^ 2) ≤ isingZ L K := by
  have h := Finset.single_le_sum (f := fun σ : Config L => Real.exp (K * bondSum σ))
    (fun σ _ => (Real.exp_pos _).le) (Finset.mem_univ (fun _ => true : Config L))
  simp only [bondSum_allUp] at h
  calc Real.exp (2 * K * (L : ℝ) ^ 2) = Real.exp (K * (2 * (L : ℝ) ^ 2)) := by ring_nf
    _ ≤ _ := h

