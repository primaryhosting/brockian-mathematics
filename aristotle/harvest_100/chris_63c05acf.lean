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

/-- The adjacency matrix of the cycle graph `C₄` (vertices `0-1-2-3-0`), as a real
`4 × 4` matrix.  This is the Hückel matrix of cyclobutadiene with `α = 0`, `β = 1`. -/
def C4adj : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 1;
     1, 0, 1, 0;
     0, 1, 0, 1;
     1, 0, 1, 0]

/-- The `k`-th Hückel eigenvalue of `C₄`: `2 cos (2πk/4)`. -/
noncomputable def huckelEigenvalue (k : Fin 4) : ℝ :=
  2 * Real.cos (2 * Real.pi * (k : ℕ) / 4)

lemma huckelEigenvalue_zero : huckelEigenvalue 0 = 2 := by
  simp [huckelEigenvalue]

lemma huckelEigenvalue_one : huckelEigenvalue 1 = 0 := by
  simp only [huckelEigenvalue]
  norm_num
  rw [show (2 * Real.pi / 4 : ℝ) = Real.pi / 2 by ring, Real.cos_pi_div_two]

lemma huckelEigenvalue_two : huckelEigenvalue 2 = -2 := by
  simp only [huckelEigenvalue]
  norm_num
  rw [show (2 * Real.pi * 2 / 4 : ℝ) = Real.pi by ring, Real.cos_pi]
  norm_num

lemma huckelEigenvalue_three : huckelEigenvalue 3 = 0 := by
  simp only [huckelEigenvalue]
  norm_num
  rw [show (2 * Real.pi * 3 / 4 : ℝ) = Real.pi + Real.pi / 2 by ring, Real.cos_add,
    Real.cos_pi_div_two]
  simp

/-- Each Hückel eigenvalue of `C₄` is one of `2`, `0`, `-2`. -/
lemma huckelEigenvalue_mem (k : Fin 4) :
    huckelEigenvalue k = 2 ∨ huckelEigenvalue k = 0 ∨ huckelEigenvalue k = -2 := by
  fin_cases k
  · exact Or.inl huckelEigenvalue_zero
  · exact Or.inr (Or.inl huckelEigenvalue_one)
  · exact Or.inr (Or.inr huckelEigenvalue_two)
  · exact Or.inr (Or.inl huckelEigenvalue_three)

/-- `C4adj - μ • 1` written out explicitly. -/
lemma C4adj_sub_smul_one (mu : ℝ) :
    C4adj - mu • (1 : Matrix (Fin 4) (Fin 4) ℝ) =
      !![-mu, 1, 0, 1;
         1, -mu, 1, 0;
         0, 1, -mu, 1;
         1, 0, 1, -mu] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C4adj]

/-- The characteristic determinant of `C₄`. -/
lemma det_C4adj_sub_smul_one (mu : ℝ) :
    (C4adj - mu • (1 : Matrix (Fin 4) (Fin 4) ℝ)).det = mu ^ 4 - 4 * mu ^ 2 := by
  rw [C4adj_sub_smul_one]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix_apply,
    Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_le_castSucc]
  ring

lemma charmatrix_C4adj :
    Matrix.charmatrix C4adj =
      !![X, -1, 0, -1;
         -1, X, -1, 0;
         0, -1, X, -1;
         -1, 0, -1, X] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.charmatrix, C4adj, Matrix.diagonal]

/-- The characteristic polynomial of the `C₄` adjacency matrix is the product of
`X - 2 cos (2πk/4)` over `k = 0, 1, 2, 3`; equivalently it is `X⁴ - 4X²`. -/
theorem huckel_C4_charpoly :
    C4adj.charpoly = ∏ k : Fin 4, (X - C (huckelEigenvalue k)) := by
  have hdet : C4adj.charpoly = X ^ 4 - 4 * X ^ 2 := by
    rw [Matrix.charpoly, charmatrix_C4adj]
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix_apply,
      Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_le_castSucc]
    ring
  rw [hdet, Fin.prod_univ_four, huckelEigenvalue_zero, huckelEigenvalue_one,
    huckelEigenvalue_two, huckelEigenvalue_three]
  simp only [map_zero, map_neg, map_ofNat, sub_zero]
  ring

/-- **Hückel theory for cyclobutadiene.**  A real number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₄` if and only if `μ = 2 cos (2πk/4)` for some
`k ∈ {0, 1, 2, 3}`. -/
theorem huckel_C4 (mu : ℝ) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ C4adj.mulVec v = mu • v) ↔
      ∃ k : Fin 4, mu = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 4) := by
  have hker : (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ C4adj.mulVec v = mu • v) ↔
      (C4adj - mu • (1 : Matrix (Fin 4) (Fin 4) ℝ)).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨v, hv, hmul⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, hmul, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
    · rintro ⟨v, hv, hmul⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hmul
      exact hmul
  rw [hker, det_C4adj_sub_smul_one]
  constructor
  · intro h
    have hfac : mu ^ 2 * ((mu - 2) * (mu + 2)) = 0 := by nlinarith [h]
    rcases mul_eq_zero.1 hfac with h0 | h1
    · have hmu : mu = 0 := by
        have := sq_eq_zero_iff.1 h0
        exact this
      exact ⟨1, by rw [hmu, ← huckelEigenvalue, huckelEigenvalue_one]⟩
    · rcases mul_eq_zero.1 h1 with h2 | h3
      · have hmu : mu = 2 := by linarith [sub_eq_zero.1 h2]
        exact ⟨0, by rw [hmu, ← huckelEigenvalue, huckelEigenvalue_zero]⟩
      · have hmu : mu = -2 := by linarith [eq_neg_of_add_eq_zero_left h3]
        exact ⟨2, by rw [hmu, ← huckelEigenvalue, huckelEigenvalue_two]⟩
  · rintro ⟨k, rfl⟩
    rcases huckelEigenvalue_mem k with h | h | h <;>
      · rw [show 2 * Real.cos (2 * Real.pi * (k : ℕ) / 4) = huckelEigenvalue k from rfl, h]
        norm_num

end Chem

