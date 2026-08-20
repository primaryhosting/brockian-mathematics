/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Real

/-- The adjacency matrix of the cycle graph `C₅`, on vertex set `Fin 5` with the
cyclic (mod 5) neighbour relation. In Hückel theory (with `α = 0`, `β = 1`) this is the
Hückel matrix of the cyclic π-system of `C₅`. -/
def C5adj : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

lemma C5adj_eq : C5adj = !![0,1,0,0,1; 1,0,1,0,0; 0,1,0,1,0; 0,0,1,0,1; 1,0,0,1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C5adj] <;> decide

/-- `2 cos(2π/5) = (√5 - 1)/2`. -/
lemma two_cos_two_pi_div_five : 2 * Real.cos (2 * π / 5) = (Real.sqrt 5 - 1) / 2 := by
  have h : (2 : ℝ) * π / 5 = 2 * (π / 5) := by ring
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [h, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [h5]

/-- `2 cos(4π/5) = -(1 + √5)/2`. -/
lemma two_cos_four_pi_div_five : 2 * Real.cos (4 * π / 5) = -(1 + Real.sqrt 5) / 2 := by
  have h : (4 : ℝ) * π / 5 = π - π / 5 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_five]
  ring

/-- The adjacency matrix of `C₅` satisfies the polynomial
`x³ - x² - 3x + 2 = (x - 2)(x² + x - 1)`. -/
lemma C5adj_min_poly :
    C5adj ^ 3 = C5adj ^ 2 + (3 : ℝ) • C5adj - (2 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
  rw [C5adj_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

lemma C5adj_pow_mulVec {μ : ℝ} {v : Fin 5 → ℝ} (h : C5adj *ᵥ v = μ • v) :
    ∀ n : ℕ, (C5adj ^ n) *ᵥ v = (μ ^ n) • v := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]

/-- Every eigenvalue `μ` of the `C₅` adjacency matrix satisfies `(μ - 2)(μ² + μ - 1) = 0`. -/
lemma eigenvalue_poly {μ : ℝ} {v : Fin 5 → ℝ} (hv : v ≠ 0) (h : C5adj *ᵥ v = μ • v) :
    (μ - 2) * (μ ^ 2 + μ - 1) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv (funext fun i => hc i)
  have key := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℝ => M *ᵥ v) C5adj_min_poly
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    C5adj_pow_mulVec h, h] at key
  have hki := congrFun key i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hki
  have : (μ ^ 3 - μ ^ 2 - 3 * μ + 2) * v i = 0 := by linear_combination hki
  have hpoly : μ ^ 3 - μ ^ 2 - 3 * μ + 2 = 0 := by
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · exact absurd h0 hi
  nlinarith [hpoly]

/-- `2` is an eigenvalue of the `C₅` adjacency matrix (the all-ones eigenvector). -/
lemma eigvec_two : ∃ v : Fin 5 → ℝ, v ≠ 0 ∧ C5adj *ᵥ v = (2 : ℝ) • v := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro hc
    have := congrFun hc 0
    norm_num at this
  · funext i
    fin_cases i <;>
      simp [C5adj_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num

/-- Any root `t` of `x² + x - 1` is an eigenvalue of the `C₅` adjacency matrix. -/
lemma eigvec_of_root (t : ℝ) (ht : t ^ 2 + t - 1 = 0) :
    ∃ v : Fin 5 → ℝ, v ≠ 0 ∧ C5adj *ᵥ v = t • v := by
  refine ⟨![1, t / 2, -(t + 1) / 2, -(t + 1) / 2, t / 2], ?_, ?_⟩
  · intro hc
    have := congrFun hc 0
    norm_num at this
  · funext i
    fin_cases i <;>
      simp [C5adj_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> nlinarith [ht]

/-- The Hückel eigenvalue problem for the cycle `C₅`: a real number `μ` is an eigenvalue of the
adjacency matrix of `C₅` if and only if `μ = 2 cos(2πk/5)` for some `k ∈ {0, 1, 2, 3, 4}`. -/
theorem huckel_C5 (μ : ℝ) :
    (∃ v : Fin 5 → ℝ, v ≠ 0 ∧ C5adj *ᵥ v = μ • v) ↔
      ∃ k : Fin 5, μ = 2 * Real.cos (2 * π * (k : ℕ) / 5) := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have e0 : 2 * Real.cos (2 * π * ((0 : ℕ) : ℝ) / 5) = 2 := by norm_num
  have e1 : 2 * Real.cos (2 * π * ((1 : ℕ) : ℝ) / 5) = (Real.sqrt 5 - 1) / 2 := by
    rw [show (2 : ℝ) * π * ((1 : ℕ) : ℝ) / 5 = 2 * π / 5 by push_cast; ring,
      two_cos_two_pi_div_five]
  have e2 : 2 * Real.cos (2 * π * ((2 : ℕ) : ℝ) / 5) = -(1 + Real.sqrt 5) / 2 := by
    rw [show (2 : ℝ) * π * ((2 : ℕ) : ℝ) / 5 = 4 * π / 5 by push_cast; ring,
      two_cos_four_pi_div_five]
  have e3 : 2 * Real.cos (2 * π * ((3 : ℕ) : ℝ) / 5) = -(1 + Real.sqrt 5) / 2 := by
    rw [show (2 : ℝ) * π * ((3 : ℕ) : ℝ) / 5 = 2 * π - 4 * π / 5 by push_cast; ring,
      Real.cos_two_pi_sub, two_cos_four_pi_div_five]
  have e4 : 2 * Real.cos (2 * π * ((4 : ℕ) : ℝ) / 5) = (Real.sqrt 5 - 1) / 2 := by
    rw [show (2 : ℝ) * π * ((4 : ℕ) : ℝ) / 5 = 2 * π - 2 * π / 5 by push_cast; ring,
      Real.cos_two_pi_sub, two_cos_two_pi_div_five]
  have hroot : ∀ t : ℝ, t = (Real.sqrt 5 - 1) / 2 ∨ t = -(1 + Real.sqrt 5) / 2 →
      t ^ 2 + t - 1 = 0 := by
    rintro t (rfl | rfl) <;> nlinarith [h5]
  constructor
  · rintro ⟨v, hv, hmul⟩
    have hpoly := eigenvalue_poly hv hmul
    rcases mul_eq_zero.mp hpoly with h0 | h0
    · refine ⟨0, ?_⟩
      show μ = 2 * Real.cos (2 * π * ((0 : ℕ) : ℝ) / 5)
      rw [e0]; linarith
    · -- μ² + μ - 1 = 0, so 2μ + 1 = ±√5
      have hsq : (2 * μ + 1) ^ 2 = Real.sqrt 5 ^ 2 := by rw [h5]; nlinarith [h0]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
      · refine ⟨1, ?_⟩
        show μ = 2 * Real.cos (2 * π * ((1 : ℕ) : ℝ) / 5)
        rw [e1]; linarith
      · refine ⟨2, ?_⟩
        show μ = 2 * Real.cos (2 * π * ((2 : ℕ) : ℝ) / 5)
        rw [e2]; linarith
  · rintro ⟨k, hk⟩
    have hklt : (k : ℕ) < 5 := k.isLt
    have hcases : (k : ℕ) = 0 ∨ (k : ℕ) = 1 ∨ (k : ℕ) = 2 ∨ (k : ℕ) = 3 ∨ (k : ℕ) = 4 := by
      omega
    rcases hcases with h | h | h | h | h <;> rw [h] at hk
    · rw [e0] at hk; subst hk; exact eigvec_two
    · rw [e1] at hk; subst hk; exact eigvec_of_root _ (hroot _ (Or.inl rfl))
    · rw [e2] at hk; subst hk; exact eigvec_of_root _ (hroot _ (Or.inr rfl))
    · rw [e3] at hk; subst hk; exact eigvec_of_root _ (hroot _ (Or.inr rfl))
    · rw [e4] at hk; subst hk; exact eigvec_of_root _ (hroot _ (Or.inl rfl))

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

