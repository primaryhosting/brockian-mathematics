import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the header block
-- above appears immediately after the single `import Mathlib` line.)

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-- The adjacency matrix of the cycle graph `C₅` written out explicitly. -/
lemma adjMatrix_cycleGraph_five :
    (SimpleGraph.cycleGraph 5).adjMatrix ℝ =
      !![0, 1, 0, 0, 1;
         1, 0, 1, 0, 0;
         0, 1, 0, 1, 0;
         0, 0, 1, 0, 1;
         1, 0, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SimpleGraph.adjMatrix_apply] <;> decide

/-- The characteristic matrix `X • 1 - A` of the adjacency matrix of `C₅`. -/
lemma charmatrix_cycleGraph_five :
    Matrix.charmatrix ((SimpleGraph.cycleGraph 5).adjMatrix ℝ) =
      !![X, -1, 0, 0, -1;
         -1, X, -1, 0, 0;
         0, -1, X, -1, 0;
         0, 0, -1, X, -1;
         -1, 0, 0, -1, X] := by
  rw [adjMatrix_cycleGraph_five]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.charmatrix]

/-- The characteristic polynomial of the adjacency matrix of `C₅` is `X⁵ - 5X³ + 5X - 2`. -/
lemma charpoly_cycleGraph_five :
    ((SimpleGraph.cycleGraph 5).adjMatrix ℝ).charpoly = X ^ 5 - 5 * X ^ 3 + 5 * X - 2 := by
  rw [Matrix.charpoly, charmatrix_cycleGraph_five]
  simp +decide [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- `cos (2π/5) = (√5 - 1)/4`. -/
lemma cos_two_pi_div_five : Real.cos (2 * π / 5) = (√5 - 1) / 4 := by
  have h : (2 : ℝ) * π / 5 = 2 * (π / 5) := by ring
  rw [h, Real.cos_two_mul, Real.cos_pi_div_five]
  have h5 : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- `cos (4π/5) = -(1 + √5)/4`. -/
lemma cos_four_pi_div_five : Real.cos (4 * π / 5) = -(1 + √5) / 4 := by
  have h : (4 : ℝ) * π / 5 = π - π / 5 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_five]
  ring

/-- `cos (6π/5) = -(1 + √5)/4`. -/
lemma cos_six_pi_div_five : Real.cos (6 * π / 5) = -(1 + √5) / 4 := by
  have h : (6 : ℝ) * π / 5 = 2 * π - (π - π / 5) := by ring
  rw [h, Real.cos_two_pi_sub, Real.cos_pi_sub, Real.cos_pi_div_five]
  ring

/-- `cos (8π/5) = (√5 - 1)/4`. -/
lemma cos_eight_pi_div_five : Real.cos (8 * π / 5) = (√5 - 1) / 4 := by
  have h : (8 : ℝ) * π / 5 = 2 * π - 2 * (π / 5) := by ring
  rw [h, Real.cos_two_pi_sub, Real.cos_two_mul, Real.cos_pi_div_five]
  have h5 : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- The two nontrivial Hückel eigenvalues of `C₅` are the roots of `X² + X - 1`. -/
lemma quadratic_factor :
    (X - C ((√5 - 1) / 2)) * (X - C (-(1 + √5) / 2)) = (X ^ 2 + X - 1 : ℝ[X]) := by
  have hs : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have e1 : ((√5 - 1) / 2) + (-(1 + √5) / 2) = -1 := by ring
  have e2 : ((√5 - 1) / 2) * (-(1 + √5) / 2) = -1 := by nlinarith [hs]
  have key : (X - C ((√5 - 1) / 2)) * (X - C (-(1 + √5) / 2))
      = X ^ 2 - C (((√5 - 1) / 2) + (-(1 + √5) / 2)) * X
          + C (((√5 - 1) / 2) * (-(1 + √5) / 2)) := by
    rw [C_add, C_mul]; ring
  rw [key, e1, e2]
  simp
  ring

/-- The product of the linear factors `X - 2 cos (2πk/5)` over `k = 0, …, 4`. -/
lemma prod_factors_eq :
    (∏ k : Fin 5, (X - C (2 * Real.cos (2 * π * ((k : ℕ) : ℝ) / 5)))) =
      X ^ 5 - 5 * X ^ 3 + 5 * X - 2 := by
  have A0 : (2 : ℝ) * π * ((((0 : Fin 5)) : ℕ) : ℝ) / 5 = 0 := by norm_num
  have A1 : (2 : ℝ) * π * ((((1 : Fin 5)) : ℕ) : ℝ) / 5 = 2 * π / 5 := by norm_num
  have A2 : (2 : ℝ) * π * ((((2 : Fin 5)) : ℕ) : ℝ) / 5 = 4 * π / 5 := by norm_num; ring
  have A3 : (2 : ℝ) * π * ((((3 : Fin 5)) : ℕ) : ℝ) / 5 = 6 * π / 5 := by norm_num; ring
  have A4 : (2 : ℝ) * π * ((((4 : Fin 5)) : ℕ) : ℝ) / 5 = 8 * π / 5 := by norm_num; ring
  have B0 : (2 : ℝ) * 1 = 2 := by norm_num
  have B1 : (2 : ℝ) * ((√5 - 1) / 4) = (√5 - 1) / 2 := by ring
  have B2 : (2 : ℝ) * (-(1 + √5) / 4) = -(1 + √5) / 2 := by ring
  rw [Fin.prod_univ_five, A0, A1, A2, A3, A4, Real.cos_zero, cos_two_pi_div_five,
    cos_four_pi_div_five, cos_six_pi_div_five, cos_eight_pi_div_five, B0, B1, B2]
  rw [show (X - C 2) * (X - C ((√5 - 1) / 2)) * (X - C (-(1 + √5) / 2))
        * (X - C (-(1 + √5) / 2)) * (X - C ((√5 - 1) / 2))
      = (X - C 2) * ((X - C ((√5 - 1) / 2)) * (X - C (-(1 + √5) / 2)))
        * ((X - C ((√5 - 1) / 2)) * (X - C (-(1 + √5) / 2))) from by ring,
    quadratic_factor, C_ofNat]
  ring

/-- **Hückel theory for cyclic C₅.**  The characteristic polynomial of the adjacency matrix of
the cycle graph `C₅` splits as `∏ k, (X - 2 cos (2πk/5))`; equivalently, the adjacency
eigenvalues of `C₅`, counted with multiplicity, are `2 cos (2πk/5)` for `k = 0, …, 4`. -/
theorem huckel_C5 :
    ((SimpleGraph.cycleGraph 5).adjMatrix ℝ).charpoly =
      ∏ k : Fin 5, (X - C (2 * Real.cos (2 * π * ((k : ℕ) : ℝ) / 5))) := by
  rw [charpoly_cycleGraph_five, prod_factors_eq]

/-- A root of the characteristic polynomial of a matrix is an eigenvalue. -/
lemma exists_eigenvector_of_isRoot_charpoly {A : Matrix (Fin 5) (Fin 5) ℝ} {m : ℝ}
    (h : A.charpoly.eval m = 0) : ∃ v : Fin 5 → ℝ, v ≠ 0 ∧ A *ᵥ v = m • v := by
  rw [Matrix.eval_charpoly] at h
  have hdet : (A - (Matrix.scalar (Fin 5)) m).det = 0 := by
    have hn : A - (Matrix.scalar (Fin 5)) m = -((Matrix.scalar (Fin 5)) m - A) := by
      rw [neg_sub]
    rw [hn, Matrix.det_neg, h]
    simp
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at hv0
  rw [hv0]
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

/-- Each of the five numbers `2 cos (2πk/5)` really is an eigenvalue of the adjacency matrix of
`C₅`: there is a nonzero vector `v` with `A *ᵥ v = 2 cos (2πk/5) • v`. -/
theorem huckel_C5_hasEigenvector (k : Fin 5) :
    ∃ v : Fin 5 → ℝ, v ≠ 0 ∧
      (SimpleGraph.cycleGraph 5).adjMatrix ℝ *ᵥ v
        = (2 * Real.cos (2 * π * ((k : ℕ) : ℝ) / 5)) • v := by
  refine exists_eigenvector_of_isRoot_charpoly ?_
  rw [huckel_C5, eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
  simp

end Chem

