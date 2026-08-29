import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Matrix Polynomial

/-- The adjacency matrix of the cycle graph `C₆`, written out explicitly. -/
def A6 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 1, 0, 0, 0, 1;
     1, 0, 1, 0, 0, 0;
     0, 1, 0, 1, 0, 0;
     0, 0, 1, 0, 1, 0;
     0, 0, 0, 1, 0, 1;
     1, 0, 0, 0, 1, 0]

/-- The Hückel energies (adjacency eigenvalues) of `C₆`, in the order `k = 0,…,5`,
i.e. `2 cos (2πk/6)`. -/
def eig6 : Fin 6 → ℝ := ![2, 1, -1, -2, -1, 1]

/-- Matrix whose `k`-th column is a real eigenvector of `A6` for the eigenvalue `eig6 k`. -/
def P6 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1, 2, 2, 1, 0, 0;
     1, 1, -1, -1, 1, 1;
     1, -1, -1, 1, -1, 1;
     1, -2, 2, -1, 0, 0;
     1, -1, -1, 1, 1, -1;
     1, 1, -1, -1, -1, -1]

/-- The inverse of `P6`. -/
noncomputable def Q6 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1/6, 1/6, 1/6, 1/6, 1/6, 1/6;
     2/12, 1/12, -1/12, -2/12, -1/12, 1/12;
     2/12, -1/12, -1/12, 2/12, -1/12, -1/12;
     1/6, -1/6, 1/6, -1/6, 1/6, -1/6;
     0, 1/4, -1/4, 0, 1/4, -1/4;
     0, 1/4, 1/4, 0, -1/4, -1/4]

theorem adjMatrix_cycleGraph_six : (SimpleGraph.cycleGraph 6).adjMatrix ℝ = A6 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A6, SimpleGraph.adjMatrix_apply] <;> decide

theorem P6_mul_Q6 : P6 * Q6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P6, Q6, Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

theorem Q6_mul_P6 : Q6 * P6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P6, Q6, Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

theorem A6_mul_P6 : A6 * P6 = P6 * diagonal eig6 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A6, P6, eig6, Matrix.mul_apply, Fin.sum_univ_six, Matrix.diagonal] <;> norm_num

/-- `P6`, as a unit of the matrix ring. -/
noncomputable def U6 : (Matrix (Fin 6) (Fin 6) ℝ)ˣ :=
  ⟨P6, Q6, P6_mul_Q6, Q6_mul_P6⟩

theorem A6_conj : A6 = P6 * diagonal eig6 * Q6 := by
  calc A6 = A6 * (P6 * Q6) := by rw [P6_mul_Q6, mul_one]
    _ = A6 * P6 * Q6 := by rw [mul_assoc]
    _ = P6 * diagonal eig6 * Q6 := by rw [A6_mul_P6]

theorem charpoly_A6 : A6.charpoly = ∏ k : Fin 6, (X - C (eig6 k)) := by
  rw [A6_conj, ← Matrix.charpoly_diagonal eig6]
  exact Matrix.charpoly_units_conj U6 (diagonal eig6)

theorem eig6_eq_cos (k : Fin 6) : eig6 k = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) := by
  fin_cases k <;> simp only [eig6] <;> norm_num
  · rw [show 2 * Real.pi / 6 = Real.pi / 3 by ring, Real.cos_pi_div_three]
    norm_num
  · rw [show 2 * Real.pi * 2 / 6 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
    norm_num
  · rw [show 2 * Real.pi * 3 / 6 = Real.pi by ring, Real.cos_pi]
    norm_num
  · rw [show 2 * Real.pi * 4 / 6 = 2 * Real.pi - (Real.pi - Real.pi / 3) by ring,
      Real.cos_two_pi_sub, Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  · rw [show 2 * Real.pi * 5 / 6 = 2 * Real.pi - Real.pi / 3 by ring, Real.cos_two_pi_sub,
      Real.cos_pi_div_three]
    norm_num

/-- **Hückel theory for benzene (`C₆`).**
The characteristic polynomial of the adjacency matrix of the cycle graph `C₆` is
`∏_{k=0}^{5} (X - 2 cos (2πk/6))`; equivalently, the adjacency eigenvalues of `C₆`,
listed with multiplicity, are `2 cos (2πk/6)` for `k = 0, …, 5`
(namely `2, 1, 1, -1, -1, -2`). -/
theorem huckel_C6 :
    ((SimpleGraph.cycleGraph 6).adjMatrix ℝ).charpoly =
      ∏ k : Fin 6, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 6))) := by
  rw [adjMatrix_cycleGraph_six, charpoly_A6]
  exact Finset.prod_congr rfl fun k _ => by rw [eig6_eq_cos k]

/-- The spectrum of the adjacency matrix of `C₆` is exactly the set of numbers
`2 cos (2πk/6)`, `k = 0, …, 5`. -/
theorem huckel_C6_spectrum :
    spectrum ℝ ((SimpleGraph.cycleGraph 6).adjMatrix ℝ) =
      Set.range fun k : Fin 6 => 2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) := by
  ext r
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C6, Polynomial.IsRoot.def,
    Polynomial.eval_prod]
  constructor
  · intro h
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h
    refine ⟨k, ?_⟩
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hk
    exact hk.symm
  · rintro ⟨k, rfl⟩
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    simp

end Chem

