/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Chem

open Matrix

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
in units where the Coulomb integral `α` is `0` and the resonance integral `β` is `1`). -/
def C5 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 1, 0, 0, 1;
     1, 0, 1, 0, 0;
     0, 1, 0, 1, 0;
     0, 0, 1, 0, 1;
     1, 0, 0, 1, 0]

/-- `C₅`'s adjacency matrix satisfies its minimal polynomial `x³ - x² - 3x + 2`. -/
lemma C5_pow_three : C5 ^ 3 = C5 ^ 2 + (3 : ℝ) • C5 - (2 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C5, pow_succ, Matrix.mul_apply, Fin.sum_univ_five] <;> norm_num

/-- `cos (2π/5) = (√5 - 1)/4`. -/
lemma cos_two_pi_div_five : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
  have h : 2 * Real.pi / 5 = 2 * (Real.pi / 5) := by ring
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [h, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [h5]

/-- `cos (4π/5) = -(1 + √5)/4`. -/
lemma cos_four_pi_div_five : Real.cos (4 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4 := by
  have h : 4 * Real.pi / 5 = Real.pi - Real.pi / 5 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_five]
  ring

/-- The all-ones vector is an eigenvector of `C5` for the eigenvalue `2`. -/
lemma C5_mulVec_ones : C5 *ᵥ ![1, 1, 1, 1, 1] = (2 : ℝ) • ![1, 1, 1, 1, 1] := by
  ext i
  fin_cases i <;> simp [C5, Matrix.mulVec, dotProduct, Fin.sum_univ_five] <;> norm_num

/-- For a root `μ` of `x² + x - 1`, the vector `(2, μ, -1-μ, -1-μ, μ)` is an eigenvector of `C5`
for the eigenvalue `μ`. -/
lemma C5_mulVec_root (μ : ℝ) (h : μ ^ 2 + μ - 1 = 0) :
    C5 *ᵥ ![2, μ, -1 - μ, -1 - μ, μ] = μ • ![2, μ, -1 - μ, -1 - μ, μ] := by
  ext i
  fin_cases i <;> simp [C5, Matrix.mulVec, dotProduct, Fin.sum_univ_five] <;> nlinarith [h]

/-- Every eigenvalue of `C5` is a root of `x³ - x² - 3x + 2 = (x - 2)(x² + x - 1)`. -/
lemma eigenvalue_poly {μ : ℝ} {v : Fin 5 → ℝ} (hv : v ≠ 0) (heq : C5 *ᵥ v = μ • v) :
    μ ^ 3 - μ ^ 2 - 3 * μ + 2 = 0 := by
  have h2 : C5 ^ 2 *ᵥ v = μ ^ 2 • v := by
    rw [pow_two, ← Matrix.mulVec_mulVec, heq, Matrix.mulVec_smul, heq, smul_smul, ← pow_two]
  have h3 : C5 ^ 3 *ᵥ v = μ ^ 3 • v := by
    rw [pow_succ, ← Matrix.mulVec_mulVec, heq, Matrix.mulVec_smul, h2, smul_smul]
    ring_nf
  have hmul : C5 ^ 3 *ᵥ v = (C5 ^ 2 + (3 : ℝ) • C5 - (2 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ)) *ᵥ v := by
    rw [← C5_pow_three]
  rw [h3, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, h2, heq,
    Matrix.one_mulVec] at hmul
  have hkey : (μ ^ 3 - μ ^ 2 - 3 * μ + 2) • v = 0 := by
    ext i
    have hi := congrFun hmul i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
    linear_combination hi
  rcases smul_eq_zero.mp hkey with h | h
  · exact h
  · exact absurd h hv

theorem huckel_C5 (μ : ℝ) :
    (∃ v : Fin 5 → ℝ, v ≠ 0 ∧ C5 *ᵥ v = μ • v) ↔
      ∃ k : Fin 5, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 5) := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hc0 : Real.cos (2 * Real.pi * ((0 : Fin 5) : ℕ) / 5) = 1 := by norm_num
  have hc1 : Real.cos (2 * Real.pi * ((1 : Fin 5) : ℕ) / 5) = (Real.sqrt 5 - 1) / 4 := by
    have : (2 * Real.pi * ((1 : Fin 5) : ℕ) / 5) = 2 * Real.pi / 5 := by norm_num
    rw [this, cos_two_pi_div_five]
  have hc2 : Real.cos (2 * Real.pi * ((2 : Fin 5) : ℕ) / 5) = -(1 + Real.sqrt 5) / 4 := by
    have : (2 * Real.pi * ((2 : Fin 5) : ℕ) / 5) = 4 * Real.pi / 5 := by
      norm_num; ring
    rw [this, cos_four_pi_div_five]
  have hc3 : Real.cos (2 * Real.pi * ((3 : Fin 5) : ℕ) / 5) = -(1 + Real.sqrt 5) / 4 := by
    have h : (2 * Real.pi * ((3 : Fin 5) : ℕ) / 5) = 2 * Real.pi - 4 * Real.pi / 5 := by
      norm_num; ring
    rw [h, Real.cos_two_pi_sub, cos_four_pi_div_five]
  have hc4 : Real.cos (2 * Real.pi * ((4 : Fin 5) : ℕ) / 5) = (Real.sqrt 5 - 1) / 4 := by
    have h : (2 * Real.pi * ((4 : Fin 5) : ℕ) / 5) = 2 * Real.pi - 2 * Real.pi / 5 := by
      norm_num; ring
    rw [h, Real.cos_two_pi_sub, cos_two_pi_div_five]
  constructor
  · rintro ⟨v, hv, heq⟩
    have hpoly := eigenvalue_poly hv heq
    have hfac : (μ - 2) * (μ ^ 2 + μ - 1) = 0 := by linear_combination hpoly
    rcases mul_eq_zero.mp hfac with h | h
    · refine ⟨0, ?_⟩
      rw [hc0]
      linarith
    · have hsq : (2 * μ + 1 - Real.sqrt 5) * (2 * μ + 1 + Real.sqrt 5) = 0 := by
        linear_combination 4 * h - h5
      rcases mul_eq_zero.mp hsq with h' | h'
      · exact ⟨1, by rw [hc1]; linarith⟩
      · exact ⟨2, by rw [hc2]; linarith⟩
  · rintro ⟨k, hk⟩
    have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by fin_cases k <;> simp
    have main : μ = 2 ∨ μ ^ 2 + μ - 1 = 0 := by
      rcases hk5 with rfl | rfl | rfl | rfl | rfl
      · left; rw [hk, hc0]; norm_num
      · right; rw [hk, hc1]; nlinarith [h5]
      · right; rw [hk, hc2]; nlinarith [h5]
      · right; rw [hk, hc3]; nlinarith [h5]
      · right; rw [hk, hc4]; nlinarith [h5]
    rcases main with h | h
    · refine ⟨![1, 1, 1, 1, 1], ?_, ?_⟩
      · intro hzero
        have := congrFun hzero 0
        simp at this
      · rw [h]; exact C5_mulVec_ones
    · refine ⟨![2, μ, -1 - μ, -1 - μ, μ], ?_, C5_mulVec_root μ h⟩
      intro hzero
      have := congrFun hzero 0
      simp at this

/-- Explicit form of the C₅ spectrum: the eigenvalues of the adjacency matrix of `C₅` are
exactly `2` (from `k = 0`), `(√5 - 1)/2` (from `k = 1, 4`) and `-(1 + √5)/2` (from `k = 2, 3`). -/
theorem huckel_C5_explicit (μ : ℝ) :
    (∃ v : Fin 5 → ℝ, v ≠ 0 ∧ C5 *ᵥ v = μ • v) ↔
      μ = 2 ∨ μ = (Real.sqrt 5 - 1) / 2 ∨ μ = -(1 + Real.sqrt 5) / 2 := by
  rw [huckel_C5]
  constructor
  · rintro ⟨k, hk⟩
    have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by fin_cases k <;> simp
    have hc0 : Real.cos (2 * Real.pi * ((0 : Fin 5) : ℕ) / 5) = 1 := by norm_num
    have hc1 : Real.cos (2 * Real.pi * ((1 : Fin 5) : ℕ) / 5) = (Real.sqrt 5 - 1) / 4 := by
      have : (2 * Real.pi * ((1 : Fin 5) : ℕ) / 5) = 2 * Real.pi / 5 := by norm_num
      rw [this, cos_two_pi_div_five]
    have hc2 : Real.cos (2 * Real.pi * ((2 : Fin 5) : ℕ) / 5) = -(1 + Real.sqrt 5) / 4 := by
      have : (2 * Real.pi * ((2 : Fin 5) : ℕ) / 5) = 4 * Real.pi / 5 := by norm_num; ring
      rw [this, cos_four_pi_div_five]
    have hc3 : Real.cos (2 * Real.pi * ((3 : Fin 5) : ℕ) / 5) = -(1 + Real.sqrt 5) / 4 := by
      have h : (2 * Real.pi * ((3 : Fin 5) : ℕ) / 5) = 2 * Real.pi - 4 * Real.pi / 5 := by
        norm_num; ring
      rw [h, Real.cos_two_pi_sub, cos_four_pi_div_five]
    have hc4 : Real.cos (2 * Real.pi * ((4 : Fin 5) : ℕ) / 5) = (Real.sqrt 5 - 1) / 4 := by
      have h : (2 * Real.pi * ((4 : Fin 5) : ℕ) / 5) = 2 * Real.pi - 2 * Real.pi / 5 := by
        norm_num; ring
      rw [h, Real.cos_two_pi_sub, cos_two_pi_div_five]
    rcases hk5 with rfl | rfl | rfl | rfl | rfl
    · left; rw [hk, hc0]; norm_num
    · right; left; rw [hk, hc1]; ring
    · right; right; rw [hk, hc2]; ring
    · right; right; rw [hk, hc3]; ring
    · right; left; rw [hk, hc4]; ring
  · rintro (rfl | rfl | rfl)
    · refine ⟨0, ?_⟩; norm_num
    · refine ⟨1, ?_⟩
      have h : (2 * Real.pi * ((1 : Fin 5) : ℕ) / 5) = 2 * Real.pi / 5 := by norm_num
      rw [h, cos_two_pi_div_five]; ring
    · refine ⟨2, ?_⟩
      have h : (2 * Real.pi * ((2 : Fin 5) : ℕ) / 5) = 4 * Real.pi / 5 := by norm_num; ring
      rw [h, cos_four_pi_div_five]; ring

end Chem

