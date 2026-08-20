/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Real

namespace Frontier

/-- A Boolean spin variable read as a real number `±1`. -/

lemma onsagerIntegrand_eq_zero_iff {K : ℝ} (hK : 0 ≤ K) :
    (∃ θ₁ θ₂ : ℝ, onsagerIntegrand K θ₁ θ₂ = 0) ↔ K = onsagerKc := by
  constructor
  · rintro ⟨θ₁, θ₂, h0⟩
    have hle := sq_sinh_sub_one_le_onsagerIntegrand hK θ₁ θ₂
    rw [h0] at hle
    have hsq : (Real.sinh (2 * K) - 1) ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
    have hsinh : Real.sinh (2 * K) = 1 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
      linarith
    have : Real.sinh (2 * K) = Real.sinh (2 * onsagerKc) := by
      rw [hsinh, sinh_two_onsagerKc]
    have := Real.sinh_injective this
    linarith
  · rintro rfl
    refine ⟨0, 0, ?_⟩
    have hsinh := sinh_two_onsagerKc
    have hc : Real.cosh (2 * onsagerKc) ^ 2 = Real.sinh (2 * onsagerKc) ^ 2 + 1 := by
      rw [Real.cosh_sq']; ring
    unfold onsagerIntegrand
    rw [hsinh] at hc ⊢
    simp [hc]

/-- At infinite temperature (`K = 0`) the Onsager formula gives `log 2` per site. -/
