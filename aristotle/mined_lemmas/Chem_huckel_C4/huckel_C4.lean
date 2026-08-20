/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial

/-- The Hückel matrix of the carbon skeleton of cyclobutadiene, in units where the Coulomb
integral `α` is `0` and the resonance integral `β` is `1`: the adjacency matrix of the cycle
graph `C₄`. -/

theorem huckel_C4 :
    C4adj.charpoly = ∏ k ∈ Finset.range 4, (X - C (2 * Real.cos (2 * π * k / 4))) ∧
      ∀ μ : ℝ, (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ C4adj.mulVec v = μ • v) ↔
        ∃ k ∈ Finset.range 4, μ = 2 * Real.cos (2 * π * k / 4) := by
  refine ⟨by rw [C4adj_charpoly, prod_cos_factors], fun μ => ?_⟩
  rw [exists_eigenvector_iff_eval_charpoly, C4adj_charpoly]
  simp only [eval_mul, eval_sub, eval_add, eval_X, eval_C, mul_eq_zero, sub_eq_zero,
    add_eq_zero_iff_eq_neg]
  constructor
  · rintro ((h | h) | h)
    · rcases h with h | h
      · exact ⟨0, by simp, by rw [cos_zero_four]; linarith⟩
      · exact ⟨1, by simp, by rw [cos_one_four]; linarith⟩
    · exact ⟨2, by simp, by rw [cos_two_four]; linarith⟩
    · exact ⟨1, by simp, by rw [cos_one_four]; linarith⟩
  · rintro ⟨k, hk, rfl⟩
    simp only [Finset.mem_range] at hk
    interval_cases k
    · rw [cos_zero_four]; norm_num
    · rw [cos_one_four]; norm_num
    · rw [cos_two_four]; norm_num
    · rw [cos_three_four]; norm_num

end Chem

