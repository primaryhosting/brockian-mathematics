/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Note: Lean requires `import` to precede any module docstring `/-! ... -/`,
so this header is a plain block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix Polynomial

/-- A primitive 10-th root of unity. -/

lemma C10_mul_Pmat : C10 * Pmat = Pmat * Matrix.diagonal eig := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal, Pmat_apply]
  simp only [C10, SimpleGraph.adjMatrix_apply, Pmat_apply]
  fin_cases i <;> norm_num +decide [Fin.sum_univ_succ] <;> rw [eig_eq k] <;>
  first
    | linear_combination row_id (i := 0) (n₁ := 1) (n₂ := 9) (k : ℕ) (by norm_num) (by norm_num)
    | linear_combination row_id (i := 1) (n₁ := 2) (n₂ := 0) (k : ℕ) (by norm_num) (by norm_num)
    | linear_combination row_id (i := 2) (n₁ := 3) (n₂ := 1) (k : ℕ) (by norm_num) (by norm_num)
    | linear_combination row_id (i := 3) (n₁ := 4) (n₂ := 2) (k : ℕ) (by norm_num) (by norm_num)
    | linear_combination row_id (i := 4) (n₁ := 5) (n₂ := 3) (k : ℕ) (by norm_num) (by norm_num)
    | linear_combination row_id (i := 5) (n₁ := 6) (n₂ := 4) (k : ℕ) (by norm_num) (by norm_num)
    | linear_combination row_id (i := 6) (n₁ := 7) (n₂ := 5) (k : ℕ) (by norm_num) (by norm_num)
    | linear_combination row_id (i := 7) (n₁ := 8) (n₂ := 6) (k : ℕ) (by norm_num) (by norm_num)
    | linear_combination row_id (i := 8) (n₁ := 9) (n₂ := 7) (k : ℕ) (by norm_num) (by norm_num)
    | linear_combination row_id (i := 9) (n₁ := 0) (n₂ := 8) (k : ℕ) (by norm_num) (by norm_num)

