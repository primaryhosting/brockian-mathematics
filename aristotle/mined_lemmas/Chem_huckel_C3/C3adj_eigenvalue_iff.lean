/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- The adjacency matrix of the cycle graph `C₃`: every pair of distinct vertices
is joined by an edge, and there are no loops. -/

lemma C3adj_eigenvalue_iff (μ : ℝ) :
    (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ C3adj.mulVec v = μ • v) ↔ (μ = 2 ∨ μ = -1) := by
  have h : (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ C3adj.mulVec v = μ • v) ↔
      (∃ v : Fin 3 → ℝ, v ≠ 0 ∧
        (C3adj - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).mulVec v = 0) := by
    constructor
    · rintro ⟨v, hv, h⟩
      exact ⟨v, hv, by rw [Matrix.sub_mulVec, h, smul_one_mulVec, sub_self]⟩
    · rintro ⟨v, hv, h⟩
      rw [Matrix.sub_mulVec, sub_eq_zero, smul_one_mulVec] at h
      exact ⟨v, hv, h⟩
  rw [h, Matrix.exists_mulVec_eq_zero_iff, C3adj_det_sub_smul]
  constructor
  · intro h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · left; linarith [neg_eq_zero.1 h1]
    · right; have := (pow_eq_zero_iff (n := 2) (by norm_num)).1 h1; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- `2 cos (2π/3) = -1`. -/
