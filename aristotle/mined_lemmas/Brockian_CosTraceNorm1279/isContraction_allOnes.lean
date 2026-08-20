import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-! ## Setup: Euclidean norm, contractions and the trace norm by duality -/

/-- The Euclidean (ℓ²) norm of a real vector indexed by `Fin n`. -/

lemma isContraction_allOnes {n : ℕ} :
    IsContraction (Matrix.of fun _ _ : Fin n => (1 / n : ℝ)) := by
  intro v
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [nrm]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmv : ∀ i, (Matrix.of (fun _ _ : Fin n => (1 / n : ℝ))).mulVec v i
      = (∑ j, v j) / n := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, one_div]
    rw [← Finset.mul_sum]
    ring
  have hcs : (∑ j, v j) ^ 2 ≤ n * ∑ j, (v j) ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1 : ℝ)) v
    simpa using this
  have hle : ∑ _i : Fin n, ((∑ j, v j) / n) ^ 2 ≤ ∑ i, (v i) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow]
    have hEq : (n : ℝ) * ((∑ j, v j) ^ 2 / (n : ℝ) ^ 2) = (∑ j, v j) ^ 2 / n := by field_simp
    rw [hEq, div_le_iff₀ hn']
    nlinarith [hcs]
  simp only [nrm]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ((Matrix.of (fun _ _ : Fin n => (1 / n : ℝ))).mulVec v i) ^ 2
      = ∑ _i : Fin n, ((∑ j, v j) / n) ^ 2 := by
        exact Finset.sum_congr rfl (fun i _ => by rw [hmv i])
    _ ≤ ∑ i, (v i) ^ 2 := hle

/-- The bound `n` is attained: for zero phases the cosine matrix is the all-ones
matrix, whose trace norm is exactly `n`. -/
