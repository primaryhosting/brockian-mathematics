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
noncomputable def C4adj : Matrix (Fin 4) (Fin 4) ℝ := (SimpleGraph.cycleGraph 4).adjMatrix ℝ

/-- The adjacency matrix of `C₄`, written out explicitly. -/
lemma C4adj_eq : C4adj = !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C4adj, SimpleGraph.adjMatrix] <;> decide

/-- The characteristic polynomial of the `C₄` adjacency matrix is `X⁴ - 4X²`, presented in
factored form. -/
lemma C4adj_charpoly : C4adj.charpoly = (X - C 2) * X * (X + C 2) * X := by
  rw [C4adj_eq]
  have h1 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 := rfl
  have h3 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 := rfl
  simp +decide [Matrix.charpoly, Matrix.charmatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    h1, h3, map_ofNat]
  ring

lemma cos_zero_four : Real.cos (2 * π * (0 : ℕ) / 4) = 1 := by norm_num

lemma cos_one_four : Real.cos (2 * π * (1 : ℕ) / 4) = 0 := by
  have h : (2 * π * (1 : ℕ) / 4 : ℝ) = π / 2 := by push_cast; ring
  rw [h, Real.cos_pi_div_two]

lemma cos_two_four : Real.cos (2 * π * (2 : ℕ) / 4) = -1 := by
  have h : (2 * π * (2 : ℕ) / 4 : ℝ) = π := by push_cast; ring
  rw [h, Real.cos_pi]

lemma cos_three_four : Real.cos (2 * π * (3 : ℕ) / 4) = 0 := by
  have h : (2 * π * (3 : ℕ) / 4 : ℝ) = π + π / 2 := by push_cast; ring
  rw [h, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi]
  ring

/-- The product of the four linear factors `X - 2cos(2πk/4)`. -/
lemma prod_cos_factors :
    ∏ k ∈ Finset.range 4, (X - C (2 * Real.cos (2 * π * k / 4)))
      = (X - C 2) * X * (X + C 2) * X := by
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_succ, Finset.prod_range_zero, cos_zero_four, cos_one_four,
    cos_two_four, cos_three_four]
  norm_num

/-- A real number is an eigenvalue of a matrix (in the sense of admitting a nonzero
eigenvector) exactly when it is a root of the characteristic polynomial. -/
lemma exists_eigenvector_iff_eval_charpoly (A : Matrix (Fin 4) (Fin 4) ℝ) (μ : ℝ) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ A.mulVec v = μ • v) ↔ A.charpoly.eval μ = 0 := by
  have hs : ∀ v : Fin 4 → ℝ, (Matrix.scalar (Fin 4) μ).mulVec v = μ • v := by
    intro v
    ext i
    simp [Matrix.scalar, Matrix.mulVec_diagonal]
  rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, by rw [Matrix.sub_mulVec, h, hs, sub_self]⟩
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at h
    rw [← h, hs]

/-- **Hückel theory for cyclobutadiene (C₄).**

The characteristic polynomial of the adjacency matrix of the cycle graph `C₄` factors as
`∏_{k=0}^{3} (X - 2cos(2πk/4))`, and consequently the eigenvalues of that matrix (the real
numbers admitting a nonzero eigenvector) are exactly the numbers `2cos(2πk/4)` for
`k = 0, 1, 2, 3`, i.e. `2, 0, -2, 0`. -/
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

