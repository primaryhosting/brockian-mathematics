/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real Matrix SimpleGraph

namespace Chem

/-- The adjacency matrix (over `ℝ`) of the cycle graph `C₈`, i.e. the Hückel matrix of
cyclooctatetraene in units where `α = 0` and `β = 1`. -/
noncomputable def C8 : Matrix (Fin 8) (Fin 8) ℝ := (SimpleGraph.cycleGraph 8).adjMatrix ℝ

/-- Acting by the adjacency matrix of `C₈` is taking the sum of the two cyclic neighbours. -/
lemma C8_mulVec (v : Fin 8 → ℝ) (i : Fin 8) : (C8 *ᵥ v) i = v (i - 1) + v (i + 1) := by
  rw [C8, SimpleGraph.adjMatrix_mulVec_apply]
  have h : (SimpleGraph.cycleGraph 8).neighborFinset i = {i - 1, i + 1} :=
    SimpleGraph.cycleGraph_neighborFinset (n := 6) (v := i)
  rw [h, Finset.sum_pair]
  revert i
  decide

/-- The angle `2πk/8`. -/
noncomputable def theta (k : ℕ) : ℝ := 2 * π * k / 8

/-- `m ↦ cos (2πk m/8)`, defined on all of `ℤ`. -/
noncomputable def gk (k : ℕ) (m : ℤ) : ℝ := Real.cos (theta k * m)

lemma gk_period (k : ℕ) (m t : ℤ) : gk k (m + 8 * t) = gk k m := by
  have h : theta k * ((m + 8 * t : ℤ) : ℝ) = theta k * (m : ℝ) + (((k : ℤ) * t : ℤ) : ℝ) * (2 * π) := by
    unfold theta; push_cast; ring
  unfold gk
  rw [h, Real.cos_add_int_mul_two_pi]

lemma gk_congr (k : ℕ) {a b : ℤ} (h : a % 8 = b % 8) : gk k a = gk k b := by
  have hab : a = b + 8 * ((a - b) / 8) := by omega
  rw [hab, gk_period]

/-- The candidate eigenvector for the eigenvalue `2 cos (2πk/8)`. -/
noncomputable def vk (k : ℕ) : Fin 8 → ℝ := fun j => gk k (j.val : ℤ)

lemma vk_zero (k : ℕ) : vk k 0 = 1 := by
  simp [vk, gk]

lemma vk_ne_zero (k : ℕ) : vk k ≠ 0 := by
  intro h
  have := congrFun h 0
  rw [vk_zero] at this
  norm_num at this

lemma val_succ_mod (i : Fin 8) : (((i + 1).val : ℤ)) % 8 = ((i.val : ℤ) + 1) % 8 := by
  revert i; decide

lemma val_pred_mod (i : Fin 8) : (((i - 1).val : ℤ)) % 8 = ((i.val : ℤ) - 1) % 8 := by
  revert i; decide

/-- The eigenvector equation, componentwise. -/
lemma vk_eigen (k : ℕ) (i : Fin 8) :
    vk k (i - 1) + vk k (i + 1) = (2 * Real.cos (theta k)) * vk k i := by
  have h1 : vk k (i + 1) = gk k ((i.val : ℤ) + 1) := gk_congr k (val_succ_mod i)
  have h2 : vk k (i - 1) = gk k ((i.val : ℤ) - 1) := gk_congr k (val_pred_mod i)
  rw [h1, h2]
  simp only [vk, gk]
  push_cast
  rw [show theta k * ((i.val : ℝ) - 1) = theta k * (i.val : ℝ) - theta k by ring,
      show theta k * ((i.val : ℝ) + 1) = theta k * (i.val : ℝ) + theta k by ring,
      Real.cos_sub, Real.cos_add]
  ring

lemma C8_mulVec_vk (k : ℕ) : C8 *ᵥ vk k = (2 * Real.cos (theta k)) • vk k := by
  funext i
  rw [C8_mulVec, Pi.smul_apply, smul_eq_mul]
  exact vk_eigen k i

/-- Every `2 cos (2πk/8)` is an eigenvalue of the adjacency matrix of `C₈`. -/
lemma huckel_C8_exists (k : ℕ) :
    ∃ v : Fin 8 → ℝ, v ≠ 0 ∧ C8 *ᵥ v = (2 * Real.cos (2 * π * k / 8)) • v :=
  ⟨vk k, vk_ne_zero k, C8_mulVec_vk k⟩

-- Index arithmetic in `Fin 8`.
lemma fin8_sub_one_sub_one (i : Fin 8) : i - 1 - 1 = i - 2 := by revert i; decide
lemma fin8_sub_one_add_one (i : Fin 8) : i - 1 + 1 = i := by revert i; decide
lemma fin8_add_one_sub_one (i : Fin 8) : i + 1 - 1 = i := by revert i; decide
lemma fin8_add_one_add_one (i : Fin 8) : i + 1 + 1 = i + 2 := by revert i; decide
lemma fin8_sub_two_sub_two (i : Fin 8) : i - 2 - 2 = i + 4 := by revert i; decide
lemma fin8_sub_two_add_two (i : Fin 8) : i - 2 + 2 = i := by revert i; decide
lemma fin8_add_two_sub_two (i : Fin 8) : i + 2 - 2 = i := by revert i; decide
lemma fin8_add_two_add_two (i : Fin 8) : i + 2 + 2 = i + 4 := by revert i; decide
lemma fin8_add_four_add_four (i : Fin 8) : i + 4 + 4 = i := by revert i; decide

/-- Two steps of the recurrence. -/
lemma step2 {v : Fin 8 → ℝ} {μ : ℝ} (H : ∀ i, v (i - 1) + v (i + 1) = μ * v i) (i : Fin 8) :
    v (i - 2) + v (i + 2) = (μ ^ 2 - 2) * v i := by
  have a := H (i - 1)
  rw [fin8_sub_one_sub_one, fin8_sub_one_add_one] at a
  have b := H (i + 1)
  rw [fin8_add_one_sub_one, fin8_add_one_add_one] at b
  have c := H i
  linear_combination a + b + μ * c

/-- Four steps of the recurrence. -/
lemma step4 {v : Fin 8 → ℝ} {μ : ℝ} (H : ∀ i, v (i - 1) + v (i + 1) = μ * v i) (i : Fin 8) :
    2 * v (i + 4) = ((μ ^ 2 - 2) ^ 2 - 2) * v i := by
  have a := step2 H (i - 2)
  rw [fin8_sub_two_sub_two, fin8_sub_two_add_two] at a
  have b := step2 H (i + 2)
  rw [fin8_add_two_sub_two, fin8_add_two_add_two] at b
  have c := step2 H i
  linear_combination a + b + (μ ^ 2 - 2) * c

/-- The characteristic relation satisfied by any eigenvalue. -/
lemma eigen_poly {v : Fin 8 → ℝ} {μ : ℝ} (hv : v ≠ 0)
    (H : ∀ i, v (i - 1) + v (i + 1) = μ * v i) :
    (((μ ^ 2 - 2) ^ 2 - 2) ^ 2 - 4) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext fun i => h i)
  have a := step4 H i
  have b := step4 H (i + 4)
  rw [fin8_add_four_add_four] at b
  have key : ((((μ ^ 2 - 2) ^ 2 - 2) ^ 2 - 4)) * v i = 0 := by
    linear_combination (-((μ ^ 2 - 2) ^ 2 - 2)) * a - 2 * b
  exact (mul_eq_zero.mp key).resolve_right hi

lemma cos_values_1 : 2 * Real.cos (2 * π * (1 : ℕ) / 8) = Real.sqrt 2 := by
  rw [show 2 * π * ((1 : ℕ) : ℝ) / 8 = π / 4 by push_cast; ring, Real.cos_pi_div_four]
  ring

lemma cos_values_3 : 2 * Real.cos (2 * π * (3 : ℕ) / 8) = -Real.sqrt 2 := by
  rw [show 2 * π * ((3 : ℕ) : ℝ) / 8 = π - π / 4 by push_cast; ring, Real.cos_pi_sub,
    Real.cos_pi_div_four]
  ring

/-- **Hückel theory for cyclooctatetraene (C₈).**
A real number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₈`
if and only if `μ = 2 cos (2πk/8)` for some `k ∈ {0, …, 7}`. -/
theorem huckel_C8 (μ : ℝ) :
    (∃ v : Fin 8 → ℝ, v ≠ 0 ∧ C8 *ᵥ v = μ • v) ↔
      ∃ k : ℕ, k < 8 ∧ μ = 2 * Real.cos (2 * π * k / 8) := by
  constructor
  · rintro ⟨v, hv, hEq⟩
    have H : ∀ i, v (i - 1) + v (i + 1) = μ * v i := by
      intro i
      have := congrFun hEq i
      rwa [C8_mulVec, Pi.smul_apply, smul_eq_mul] at this
    have hp := eigen_poly hv H
    -- `μ² (μ² - 4) (μ² - 2)² = 0`
    have hfac : μ ^ 2 * (μ ^ 2 - 4) * (μ ^ 2 - 2) ^ 2 = 0 := by linear_combination hp
    rcases mul_eq_zero.mp hfac with h | h
    · rcases mul_eq_zero.mp h with h | h
      · -- μ = 0
        have hμ : μ = 0 := by nlinarith [sq_nonneg μ]
        exact ⟨2, by norm_num, by
          rw [hμ, show 2 * π * ((2 : ℕ) : ℝ) / 8 = π / 2 by push_cast; ring,
            Real.cos_pi_div_two]; ring⟩
      · -- μ = ±2
        have : (μ - 2) * (μ + 2) = 0 := by linear_combination h
        rcases mul_eq_zero.mp this with h2 | h2
        · exact ⟨0, by norm_num, by
            rw [show 2 * π * ((0 : ℕ) : ℝ) / 8 = 0 by push_cast; ring, Real.cos_zero]
            linarith⟩
        · exact ⟨4, by norm_num, by
            rw [show 2 * π * ((4 : ℕ) : ℝ) / 8 = π by push_cast; ring, Real.cos_pi]
            linarith⟩
    · -- μ = ±√2
      have h2 : μ ^ 2 = 2 := by nlinarith [sq_nonneg (μ ^ 2 - 2)]
      have : (μ - Real.sqrt 2) * (μ + Real.sqrt 2) = 0 := by
        have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        linear_combination h2 - hs
      rcases mul_eq_zero.mp this with h3 | h3
      · exact ⟨1, by norm_num, by rw [cos_values_1]; linarith⟩
      · exact ⟨3, by norm_num, by rw [cos_values_3]; linarith⟩
  · rintro ⟨k, -, rfl⟩
    exact huckel_C8_exists k

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

