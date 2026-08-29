/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Chem

open Matrix

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
in units where the Coulomb integral `α` is `0` and the resonance integral `β` is `1`). -/

theorem huckel_C5_explicit (μ : ℝ) :
    (∃ v : Fin 5 → ℝ, v ≠ 0 ∧ C5 *ᵥ v = μ • v) ↔
      μ = 2 ∨ μ = (Real.sqrt 5 - 1) / 2 ∨ μ = -(1 + Real.sqrt 5) / 2 := by
  rw [huckel_C5]
  constructor
  · rintro ⟨k, hk⟩
    have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by fin_cases k <;> simp
    have hc0 : Real.cos (2 * Real.pi * ((0 : Fin 5) : ℕ) / 5) = 1 := by norm_num
    have hc1 : Real.cos (2 * Real.pi * ((1 : Fin 5) : ℕ) / 5) = (Real.sqrt 5 - 1) / 4 := by
      have : (2 * Real.pi * ((1 : Fin 5) : ℕ) / 5) = 2 * Real.pi / 5 := by norm_num
      rw [this, cos_two_pi_div_five]
    have hc2 : Real.cos (2 * Real.pi * ((2 : Fin 5) : ℕ) / 5) = -(1 + Real.sqrt 5) / 4 := by
      have : (2 * Real.pi * ((2 : Fin 5) : ℕ) / 5) = 4 * Real.pi / 5 := by norm_num; ring
      rw [this, cos_four_pi_div_five]
    have hc3 : Real.cos (2 * Real.pi * ((3 : Fin 5) : ℕ) / 5) = -(1 + Real.sqrt 5) / 4 := by
      have h : (2 * Real.pi * ((3 : Fin 5) : ℕ) / 5) = 2 * Real.pi - 4 * Real.pi / 5 := by
        norm_num; ring
      rw [h, Real.cos_two_pi_sub, cos_four_pi_div_five]
    have hc4 : Real.cos (2 * Real.pi * ((4 : Fin 5) : ℕ) / 5) = (Real.sqrt 5 - 1) / 4 := by
      have h : (2 * Real.pi * ((4 : Fin 5) : ℕ) / 5) = 2 * Real.pi - 2 * Real.pi / 5 := by
        norm_num; ring
      rw [h, Real.cos_two_pi_sub, cos_two_pi_div_five]
    rcases hk5 with rfl | rfl | rfl | rfl | rfl
    · left; rw [hk, hc0]; norm_num
    · right; left; rw [hk, hc1]; ring
    · right; right; rw [hk, hc2]; ring
    · right; right; rw [hk, hc3]; ring
    · right; left; rw [hk, hc4]; ring
  · rintro (rfl | rfl | rfl)
    · refine ⟨0, ?_⟩; norm_num
    · refine ⟨1, ?_⟩
      have h : (2 * Real.pi * ((1 : Fin 5) : ℕ) / 5) = 2 * Real.pi / 5 := by norm_num
      rw [h, cos_two_pi_div_five]; ring
    · refine ⟨2, ?_⟩
      have h : (2 * Real.pi * ((2 : Fin 5) : ℕ) / 5) = 4 * Real.pi / 5 := by norm_num; ring
      rw [h, cos_four_pi_div_five]; ring

end Chem

