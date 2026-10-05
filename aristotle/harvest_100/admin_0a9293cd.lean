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

/-
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open SimpleGraph Matrix Real

namespace Chem

/-- The adjacency matrix of the cycle graph `C₆`, over `ℂ`
(the Hückel matrix of benzene in units where `α = 0`, `β = 1`). -/
noncomputable def C6 : Matrix (Fin 6) (Fin 6) ℂ := (cycleGraph 6).adjMatrix ℂ

/-- Explicit entries of the adjacency matrix of `C₆`. -/
lemma C6_eq :
    C6 = !![0,1,0,0,0,1; 1,0,1,0,0,0; 0,1,0,1,0,0; 0,0,1,0,1,0; 0,0,0,1,0,1; 1,0,0,0,1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C6, SimpleGraph.adjMatrix_apply] <;> decide

/-- The Hückel eigenvalues `2 cos (2πk/6)` of `C₆`. -/
noncomputable def lam (k : ℕ) : ℝ := 2 * Real.cos (2 * π * (k : ℝ) / 6)

lemma lam_zero : lam 0 = 2 := by simp [lam]

lemma lam_one : lam 1 = 1 := by
  rw [lam, show (2 * π * ((1 : ℕ) : ℝ) / 6 : ℝ) = π / 3 by push_cast; ring,
    Real.cos_pi_div_three]
  norm_num

lemma lam_two : lam 2 = -1 := by
  rw [lam, show (2 * π * ((2 : ℕ) : ℝ) / 6 : ℝ) = π - π / 3 by push_cast; ring,
    Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

lemma lam_three : lam 3 = -2 := by
  rw [lam, show (2 * π * ((3 : ℕ) : ℝ) / 6 : ℝ) = π by push_cast; ring, Real.cos_pi]
  norm_num

lemma lam_four : lam 4 = -1 := by
  rw [lam, show (2 * π * ((4 : ℕ) : ℝ) / 6 : ℝ) = π + π / 3 by push_cast; ring,
    Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
  norm_num

lemma lam_five : lam 5 = 1 := by
  rw [lam, show (2 * π * ((5 : ℕ) : ℝ) / 6 : ℝ) = -(π / 3) + 2 * π by push_cast; ring,
    Real.cos_add_two_pi, Real.cos_neg, Real.cos_pi_div_three]
  norm_num

/-- A nonzero vector witnessing an eigenvalue, built from an explicit first-coordinate-nonzero
vector. -/
private lemma eigen_of (v : Fin 6 → ℂ) (c : ℂ) (hv : v 0 ≠ 0) (h : C6 *ᵥ v = c • v) :
    ∃ w : Fin 6 → ℂ, w ≠ 0 ∧ C6 *ᵥ w = c • w :=
  ⟨v, fun hc => hv (by simp [hc]), h⟩

/-- Each `2 cos (2πk/6)`, `k = 0,…,5`, is an eigenvalue of the adjacency matrix of `C₆`. -/
lemma exists_eigenvector (k : ℕ) (hk : k < 6) :
    ∃ v : Fin 6 → ℂ, v ≠ 0 ∧ C6 *ᵥ v = ((lam k : ℝ) : ℂ) • v := by
  interval_cases k
  · rw [lam_zero]
    push_cast
    refine eigen_of ![1,1,1,1,1,1] 2 (by norm_num) ?_
    ext i
    fin_cases i <;>
      simp [C6_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> ring
  · rw [lam_one]
    push_cast
    refine eigen_of ![1,1,0,-1,-1,0] 1 (by norm_num) ?_
    ext i
    fin_cases i <;>
      simp [C6_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  · rw [lam_two]
    push_cast
    refine eigen_of ![1,-1,0,1,-1,0] (-1) (by norm_num) ?_
    ext i
    fin_cases i <;>
      simp [C6_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  · rw [lam_three]
    push_cast
    refine eigen_of ![1,-1,1,-1,1,-1] (-2) (by norm_num) ?_
    ext i
    fin_cases i <;>
      simp [C6_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> ring
  · rw [lam_four]
    push_cast
    refine eigen_of ![1,-1,0,1,-1,0] (-1) (by norm_num) ?_
    ext i
    fin_cases i <;>
      simp [C6_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  · rw [lam_five]
    push_cast
    refine eigen_of ![1,1,0,-1,-1,0] 1 (by norm_num) ?_
    ext i
    fin_cases i <;>
      simp [C6_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_six]

/-- The adjacency matrix of `C₆` satisfies `A⁴ = 5A² - 4I`. -/
lemma C6_pow_four :
    C6 * C6 * (C6 * C6)
      = (5 : ℂ) • (C6 * C6) - (4 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C6_eq, Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

/-- Any eigenvalue of the adjacency matrix of `C₆` is one of the `2 cos (2πk/6)`. -/
lemma eigenvalue_mem (μ : ℂ) (h : ∃ v : Fin 6 → ℂ, v ≠ 0 ∧ C6 *ᵥ v = μ • v) :
    ∃ k : ℕ, k < 6 ∧ μ = ((lam k : ℝ) : ℂ) := by
  obtain ⟨v, hv, hvA⟩ := h
  have h2 : (C6 * C6) *ᵥ v = (μ ^ 2) • v := by
    rw [← Matrix.mulVec_mulVec, hvA, Matrix.mulVec_smul, hvA, smul_smul]
    ring_nf
  have h4 : (C6 * C6 * (C6 * C6)) *ᵥ v = (μ ^ 4) • v := by
    rw [← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, h2, smul_smul]
    ring_nf
  rw [C6_pow_four, Matrix.sub_mulVec, smul_mulVec, smul_mulVec, h2, Matrix.one_mulVec] at h4
  have hzero : (μ ^ 4 - (5 * μ ^ 2 - 4)) • v = 0 := by
    rw [sub_smul, ← h4, smul_smul, sub_smul, sub_self]
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv (funext hc)
  have hpoly : μ ^ 4 - (5 * μ ^ 2 - 4) = 0 := by
    have := congrFun hzero i
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_eq_zero] at this
    exact this.resolve_right hi
  have hfac : (μ - 1) * (μ + 1) * (μ - 2) * (μ + 2) = 0 := by linear_combination hpoly
  rcases mul_eq_zero.mp hfac with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · rcases mul_eq_zero.mp h'' with h3 | h3
      · exact ⟨1, by norm_num, by rw [lam_one]; push_cast; linear_combination h3⟩
      · exact ⟨2, by norm_num, by rw [lam_two]; push_cast; linear_combination h3⟩
    · exact ⟨0, by norm_num, by rw [lam_zero]; push_cast; linear_combination h''⟩
  · exact ⟨3, by norm_num, by rw [lam_three]; push_cast; linear_combination h'⟩

/-- **Hückel theory for benzene (C₆).**  The eigenvalues of the adjacency matrix of the
cycle graph `C₆` are exactly the numbers `2 cos (2πk/6)` for `k = 0, …, 5`:  each of these
numbers is an eigenvalue, and every eigenvalue is of this form. -/
theorem huckel_C6 :
    (∀ k : ℕ, k < 6 → ∃ v : Fin 6 → ℂ, v ≠ 0 ∧
        (cycleGraph 6).adjMatrix ℂ *ᵥ v
          = ((2 * Real.cos (2 * π * (k : ℝ) / 6) : ℝ) : ℂ) • v) ∧
    (∀ μ : ℂ, (∃ v : Fin 6 → ℂ, v ≠ 0 ∧ (cycleGraph 6).adjMatrix ℂ *ᵥ v = μ • v) →
        ∃ k : ℕ, k < 6 ∧ μ = ((2 * Real.cos (2 * π * (k : ℝ) / 6) : ℝ) : ℂ)) :=
  ⟨exists_eigenvector, eigenvalue_mem⟩

end Chem

