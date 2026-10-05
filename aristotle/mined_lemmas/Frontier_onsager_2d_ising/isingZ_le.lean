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

theorem isingZ_le (L : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    isingZ L K ≤ 2 ^ (L * L) * Real.exp (2 * K * (L : ℝ) ^ 2) := by
  calc isingZ L K ≤ ∑ _σ : Config L, Real.exp (K * (2 * (L : ℝ) ^ 2)) := by
        refine Finset.sum_le_sum (fun σ _ => Real.exp_le_exp.2 ?_)
        exact mul_le_mul_of_nonneg_left (bondSum_le σ) hK
    _ = 2 ^ (L * L) * Real.exp (2 * K * (L : ℝ) ^ 2) := by
        simp [Finset.sum_const]; ring_nf

/-- For every ferromagnetic coupling `K ≥ 0` and every finite volume, the free-energy
density is sandwiched between `2K` (the ground-state value) and `log 2 + 2K`. -/
