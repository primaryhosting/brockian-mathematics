/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Real

namespace Chem

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`):
vertices are indexed by `Fin 5` with cyclic successor `i ↦ i + 1`, and `i, j` are adjacent
iff one is the cyclic successor of the other. -/
def C5adj : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of fun i j => if j = i + 1 ∨ i = j + 1 then 1 else 0

lemma C5adj_eq :
    C5adj = !![(0 : ℝ), 1, 0, 0, 1;
                1, 0, 1, 0, 0;
                0, 1, 0, 1, 0;
                0, 0, 1, 0, 1;
                1, 0, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C5adj]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
/-- The characteristic polynomial of the `C₅` adjacency matrix is `X⁵ - 5X³ + 5X - 2`. -/
lemma C5adj_charpoly : C5adj.charpoly = X ^ 5 - 5 * X ^ 3 + 5 * X - 2 := by
  rw [C5adj_eq]
  simp +decide [Matrix.charpoly, Matrix.charmatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.succAbove]
  ring

lemma two_cos_zero : 2 * Real.cos (2 * π * 0 / 5) = 2 := by norm_num

lemma two_cos_one : 2 * Real.cos (2 * π * 1 / 5) = (√5 - 1) / 2 := by
  have h5 : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h : (2 * π * 1 / 5) = 2 * (π / 5) := by ring
  rw [h, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [h5]

lemma two_cos_two : 2 * Real.cos (2 * π * 2 / 5) = -(1 + √5) / 2 := by
  have h : (2 * π * 2 / 5) = π - π / 5 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_five]
  ring

lemma two_cos_three : 2 * Real.cos (2 * π * 3 / 5) = -(1 + √5) / 2 := by
  have h : (2 * π * 3 / 5) = π + π / 5 := by ring
  rw [h, Real.cos_add, Real.cos_pi_div_five]
  simp
  ring

lemma two_cos_four : 2 * Real.cos (2 * π * 4 / 5) = (√5 - 1) / 2 := by
  have h5 : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h : (2 * π * 4 / 5) = 2 * π - 2 * (π / 5) := by ring
  rw [h, Real.cos_two_pi_sub, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [h5]

/-- The product `∏_{k<5} (X - 2cos(2πk/5))` equals `X⁵ - 5X³ + 5X - 2`. -/
lemma prod_two_cos :
    (∏ k ∈ Finset.range 5, (X - C (2 * Real.cos (2 * π * k / 5))))
      = X ^ 5 - 5 * X ^ 3 + 5 * X - 2 := by
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_succ, Finset.prod_range_one]
  push_cast
  rw [two_cos_zero, two_cos_one, two_cos_two, two_cos_three, two_cos_four]
  have h5 : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hab : (√5 - 1) / 2 + -(1 + √5) / 2 = -1 := by ring
  have hab2 : ((√5 - 1) / 2) * (-(1 + √5) / 2) = -1 := by nlinarith [h5]
  have e1 : ((X : ℝ[X]) - C ((√5 - 1) / 2)) * (X - C (-(1 + √5) / 2)) = X ^ 2 + X - 1 := by
    have h : ((X : ℝ[X]) - C ((√5 - 1) / 2)) * (X - C (-(1 + √5) / 2))
        = X ^ 2 - C ((√5 - 1) / 2 + -(1 + √5) / 2) * X + C (((√5 - 1) / 2) * (-(1 + √5) / 2)) := by
      simp only [map_add, map_mul]; ring
    rw [h, hab, hab2]
    simp
    ring
  have h : ((((X - C (2 : ℝ)) * (X - C ((√5 - 1) / 2))) * (X - C (-(1 + √5) / 2)))
        * (X - C (-(1 + √5) / 2))) * (X - C ((√5 - 1) / 2))
      = (X - C (2 : ℝ)) * (((X - C ((√5 - 1) / 2)) * (X - C (-(1 + √5) / 2))) ^ 2) := by ring
  rw [h, e1]
  simp only [map_ofNat]
  ring

/-- **Hückel theory for cyclopentadienyl (C₅).**
The characteristic polynomial of the adjacency matrix of the cycle graph `C₅` factors
completely as `∏_{k=0}^{4} (X - 2cos(2πk/5))`; that is, the adjacency eigenvalues of `C₅`
are exactly `2cos(2πk/5)` for `k = 0, 1, 2, 3, 4`, counted with multiplicity. -/
theorem huckel_C5 :
    C5adj.charpoly = ∏ k ∈ Finset.range 5, (X - C (2 * Real.cos (2 * π * k / 5))) := by
  rw [C5adj_charpoly, prod_two_cos]

open Matrix in
/-- Spectral form of the previous result: a real number `μ` is an eigenvalue of the `C₅`
adjacency matrix (i.e. admits a nonzero eigenvector) if and only if `μ = 2cos(2πk/5)`
for some `k < 5`. -/
theorem huckel_C5_spectrum (μ : ℝ) :
    (∃ v ≠ 0, C5adj *ᵥ v = μ • v) ↔ ∃ k : ℕ, k < 5 ∧ μ = 2 * Real.cos (2 * π * k / 5) := by
  have hs : ∀ v : Fin 5 → ℝ, (Matrix.scalar (Fin 5) μ) *ᵥ v = μ • v := by
    intro v; ext i
    simp [Matrix.scalar, Matrix.mulVec, Matrix.diagonal, dotProduct, Finset.sum_ite_eq]
  have h1 : (∃ v ≠ 0, C5adj *ᵥ v = μ • v) ↔ (Matrix.scalar (Fin 5) μ - C5adj).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨v, hv, h⟩
      exact ⟨v, hv, by rw [Matrix.sub_mulVec, hs, h, sub_self]⟩
    · rintro ⟨v, hv, h⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, hs, sub_eq_zero] at h
      exact h.symm
  rw [h1, ← Matrix.eval_charpoly, huckel_C5, Polynomial.eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k, Finset.mem_range.mp hk, by linarith [sub_eq_zero.mp h]⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨k, Finset.mem_range.mpr hk, by rw [h]; ring⟩

end Chem

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

