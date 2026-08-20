/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- The adjacency matrix of the cycle graph `C₃`: every pair of distinct vertices
is joined by an edge, and there are no loops. -/
def C3adj : Matrix (Fin 3) (Fin 3) ℝ := fun i j => if i = j then 0 else 1

/-- Characteristic determinant of `C₃`: `det (A - μ I) = -(μ - 2)(μ + 1)²`. -/
lemma C3adj_det_sub_smul (μ : ℝ) :
    (C3adj - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = -(μ - 2) * (μ + 1) ^ 2 := by
  simp [C3adj, Matrix.det_fin_three, Fin.ext_iff]
  ring

private lemma smul_one_mulVec (μ : ℝ) (v : Fin 3 → ℝ) :
    ((μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).mulVec v) = μ • v := by
  ext i
  simp [Matrix.mulVec, Matrix.one_apply, dotProduct]

/-- **Key intermediate lemma.** A real number `μ` is an eigenvalue of the adjacency
matrix of `C₃` if and only if `μ = 2` or `μ = -1`. -/
lemma C3adj_eigenvalue_iff (μ : ℝ) :
    (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ C3adj.mulVec v = μ • v) ↔ (μ = 2 ∨ μ = -1) := by
  have h : (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ C3adj.mulVec v = μ • v) ↔
      (∃ v : Fin 3 → ℝ, v ≠ 0 ∧
        (C3adj - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).mulVec v = 0) := by
    constructor
    · rintro ⟨v, hv, h⟩
      exact ⟨v, hv, by rw [Matrix.sub_mulVec, h, smul_one_mulVec, sub_self]⟩
    · rintro ⟨v, hv, h⟩
      rw [Matrix.sub_mulVec, sub_eq_zero, smul_one_mulVec] at h
      exact ⟨v, hv, h⟩
  rw [h, Matrix.exists_mulVec_eq_zero_iff, C3adj_det_sub_smul]
  constructor
  · intro h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · left; linarith [neg_eq_zero.1 h1]
    · right; have := (pow_eq_zero_iff (n := 2) (by norm_num)).1 h1; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- `2 cos (2π/3) = -1`. -/
lemma two_cos_two_pi_div_three : 2 * Real.cos (2 * Real.pi * (1 : ℝ) / 3) = -1 := by
  rw [show 2 * Real.pi * (1 : ℝ) / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]
  norm_num

/-- `2 cos (4π/3) = -1`. -/
lemma two_cos_four_pi_div_three : 2 * Real.cos (2 * Real.pi * (2 : ℝ) / 3) = -1 := by
  rw [show 2 * Real.pi * (2 : ℝ) / 3 = Real.pi + Real.pi / 3 by ring, Real.cos_add,
    Real.cos_pi_div_three]
  simp

/-- The three Hückel values `2 cos (2πk/3)`, `k = 0, 1, 2`, are exactly `2, -1, -1`. -/
lemma two_cos_two_pi_k_div_three (k : Fin 3) :
    2 * Real.cos (2 * Real.pi * (k : ℝ) / 3) = 2 ∨
      2 * Real.cos (2 * Real.pi * (k : ℝ) / 3) = -1 := by
  obtain ⟨k, hk⟩ := k
  interval_cases k
  · left; norm_num
  · right; simpa using two_cos_two_pi_div_three
  · right; simpa using two_cos_four_pi_div_three

/-- **Hückel theory for the cyclic C₃ system.**
The eigenvalues of the adjacency matrix of the cycle graph `C₃` are exactly the
numbers `2 cos (2πk/3)` for `k = 0, 1, 2`. -/
theorem huckel_C3 (μ : ℝ) :
    (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ C3adj.mulVec v = μ • v) ↔
      ∃ k : Fin 3, μ = 2 * Real.cos (2 * Real.pi * (k : ℝ) / 3) := by
  rw [C3adj_eigenvalue_iff]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by simpa using two_cos_two_pi_div_three.symm⟩
  · rintro ⟨k, rfl⟩
    exact two_cos_two_pi_k_div_three k

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

