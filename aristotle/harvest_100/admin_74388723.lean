/-
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency eigenvalues of the cycle graph `C₆` (the Hückel π-system of benzene) are
`2 cos (2πk/6)` for `k = 0, …, 5`.  This is stated as the factorization of the characteristic
polynomial of the adjacency matrix, so that eigenvalues are counted with multiplicity.

The proof diagonalizes the adjacency matrix explicitly: `A = P D P⁻¹` with `P` the (real)
matrix of eigenvectors and `D = diag(2, 1, 1, -1, -1, -2)`, then uses the Mathlib lemmas
`Matrix.charpoly_units_conj` and `Matrix.charpoly_diagonal`.
-/

namespace Chem

open Polynomial Matrix

/-- The adjacency matrix of the cycle graph `C₆`, written out explicitly. -/
def C6adj : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of ![![0, 1, 0, 0, 0, 1],
              ![1, 0, 1, 0, 0, 0],
              ![0, 1, 0, 1, 0, 0],
              ![0, 0, 1, 0, 1, 0],
              ![0, 0, 0, 1, 0, 1],
              ![1, 0, 0, 0, 1, 0]]

/-- Matrix of eigenvectors of `C6adj` (the columns are the eigenvectors). -/
def C6P : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of ![![1,  2,  0,  2,  0,  1],
              ![1,  1,  1, -1,  1, -1],
              ![1, -1,  1, -1, -1,  1],
              ![1, -2,  0,  2,  0, -1],
              ![1, -1, -1, -1,  1,  1],
              ![1,  1, -1, -1, -1, -1]]

/-- The inverse of `C6P`: its rows are the eigenvectors divided by their squared norms. -/
noncomputable def C6Q : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of ![![1/6,   1/6,   1/6,   1/6,   1/6,   1/6],
              ![2/12,  1/12, -1/12, -2/12, -1/12,  1/12],
              ![0,     1/4,   1/4,   0,    -1/4,  -1/4],
              ![2/12, -1/12, -1/12,  2/12, -1/12, -1/12],
              ![0,     1/4,  -1/4,   0,     1/4,  -1/4],
              ![1/6,  -1/6,   1/6,  -1/6,   1/6,  -1/6]]

/-- The diagonal matrix of eigenvalues of `C6adj`. -/
def C6D : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.diagonal ![2, 1, 1, -1, -1, -2]

/-- The product `C6P * C6D`, written out explicitly. -/
def C6PD : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of ![![2,  2,  0, -2,  0, -2],
              ![2,  1,  1,  1, -1,  2],
              ![2, -1,  1,  1,  1, -2],
              ![2, -2,  0, -2,  0,  2],
              ![2, -1, -1,  1, -1, -2],
              ![2,  1, -1,  1,  1,  2]]

lemma adjMatrix_cycleGraph_six : (SimpleGraph.cycleGraph 6).adjMatrix ℝ = C6adj := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SimpleGraph.adjMatrix_apply, C6adj] <;> decide

lemma C6P_mul_C6Q : C6P * C6Q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C6P, C6Q, Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

lemma C6Q_mul_C6P : C6Q * C6P = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C6P, C6Q, Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

/-- The eigenvector matrix as a unit of the matrix ring. -/
noncomputable def C6Punit : (Matrix (Fin 6) (Fin 6) ℝ)ˣ :=
  ⟨C6P, C6Q, C6P_mul_C6Q, C6Q_mul_C6P⟩

lemma C6P_mul_C6D : C6P * C6D = C6PD := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C6P, C6D, C6PD, Matrix.mul_apply, Matrix.diagonal_apply]

lemma C6PD_mul_C6Q : C6PD * C6Q = C6adj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C6PD, C6Q, C6adj, Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

lemma C6adj_conj : C6adj = C6P * C6D * C6Q := by
  rw [C6P_mul_C6D, C6PD_mul_C6Q]

lemma C6adj_charpoly :
    C6adj.charpoly = ∏ i : Fin 6, (X - C (![(2:ℝ), 1, 1, -1, -1, -2] i)) := by
  rw [C6adj_conj]
  have h : C6P * C6D * C6Q = (C6Punit : Matrix (Fin 6) (Fin 6) ℝ) * C6D *
      ((C6Punit⁻¹ : (Matrix (Fin 6) (Fin 6) ℝ)ˣ) : Matrix (Fin 6) (Fin 6) ℝ) := rfl
  rw [h, Matrix.charpoly_units_conj, C6D, Matrix.charpoly_diagonal]

/-- The six numbers `2 cos (2πk/6)`, `k = 0, …, 5`, are `2, 1, -1, -2, -1, 1`. -/
lemma two_cos_vals (k : Fin 6) :
    2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) = ![(2:ℝ), 1, -1, -2, -1, 1] k := by
  have hpi3 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  fin_cases k <;> norm_num
  · rw [show (2:ℝ) * Real.pi / 6 = Real.pi / 3 by ring, hpi3]
    norm_num
  · rw [show (2:ℝ) * Real.pi * 2 / 6 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, hpi3]
    norm_num
  · rw [show (2:ℝ) * Real.pi * 3 / 6 = Real.pi by ring, Real.cos_pi]
    norm_num
  · rw [show (2:ℝ) * Real.pi * 4 / 6 = 2 * Real.pi - (Real.pi - Real.pi / 3) by ring,
      Real.cos_two_pi_sub, Real.cos_pi_sub, hpi3]
    norm_num
  · rw [show (2:ℝ) * Real.pi * 5 / 6 = 2 * Real.pi - Real.pi / 3 by ring,
      Real.cos_two_pi_sub, hpi3]
    norm_num

/-- **Hückel theory for benzene (C₆).**
The characteristic polynomial of the adjacency matrix of the cycle graph `C₆` factors as
`∏_{k=0}^{5} (X - 2 cos (2πk/6))`; equivalently, the adjacency eigenvalues of `C₆`, counted
with multiplicity, are exactly `2 cos (2πk/6)` for `k = 0, …, 5`. -/
theorem huckel_C6 :
    ((SimpleGraph.cycleGraph 6).adjMatrix ℝ).charpoly =
      ∏ k : Fin 6, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 6))) := by
  rw [adjMatrix_cycleGraph_six, C6adj_charpoly,
    Finset.prod_congr rfl (fun k _ => by rw [two_cos_vals k] :
      ∀ k ∈ Finset.univ, (X - C (2 * Real.cos (2 * Real.pi * ((k : Fin 6) : ℕ) / 6)))
        = (X - C (![(2:ℝ), 1, -1, -2, -1, 1] k)))]
  simp only [Fin.prod_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

end Chem

