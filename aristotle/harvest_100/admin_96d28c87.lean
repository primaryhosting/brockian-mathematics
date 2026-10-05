/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

/-- The adjacency matrix of the cycle graph `C₃` (every pair of distinct vertices
is adjacent). In Hückel theory this is the (shifted, scaled) Hamiltonian of the
cyclic three-carbon π-system. -/
def C3adj : Matrix (Fin 3) (Fin 3) ℝ := fun i j => if i = j then 0 else 1

lemma cos_one : 2 * Real.cos (2 * Real.pi * (1 : ℕ) / 3) = -1 := by
  have h : 2 * Real.pi * (1 : ℕ) / 3 = Real.pi - Real.pi / 3 := by
    push_cast; ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

lemma cos_two : 2 * Real.cos (2 * Real.pi * (2 : ℕ) / 3) = -1 := by
  have h : 2 * Real.pi * (2 : ℕ) / 3 = Real.pi + Real.pi / 3 := by
    push_cast; ring
  rw [h, Real.cos_add, Real.cos_pi_div_three, Real.sin_pi, Real.cos_pi]
  norm_num

lemma exists_cos_iff (μ : ℝ) :
    (∃ k : Fin 3, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 3)) ↔ (μ = 2 ∨ μ = -1) := by
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · left; norm_num
    · right; simpa using cos_one
    · right; simpa using cos_two
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by simpa using cos_one.symm⟩

lemma C3adj_det_sub (μ : ℝ) :
    (C3adj - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = -(μ - 2) * (μ + 1) ^ 2 := by
  simp [Matrix.det_fin_three, C3adj, Matrix.sub_apply, Matrix.smul_apply, Fin.ext_iff]
  ring

/-- **Hückel theory for the cyclic three-carbon π-system.**
A real number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₃`
if and only if it is of the form `2 * cos (2πk/3)` for some `k ∈ {0, 1, 2}`. -/
theorem huckel_C3 (μ : ℝ) :
    (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ C3adj.mulVec v = μ • v) ↔
      ∃ k : Fin 3, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 3) := by
  have key : (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ C3adj.mulVec v = μ • v) ↔
      (C3adj - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨v, hv, h⟩
      exact ⟨v, hv, by
        simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h]⟩
    · rintro ⟨v, hv, h⟩
      refine ⟨v, hv, ?_⟩
      simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
        using h
  rw [key, C3adj_det_sub, exists_cos_iff]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · left; linarith [neg_eq_zero.mp h]
    · right; have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h; linarith
  · rintro (rfl | rfl) <;> norm_num

/-! ## Explicit Hückel eigenvectors (Bloch waves)

The eigenvectors of the C₃ adjacency matrix are the discrete Fourier (Bloch) vectors
`v_k(j) = ω^{jk}` with `ω = exp(2πi/3)`, whose eigenvalue is exactly `2cos(2πk/3)`.
This is the standard Hückel description of the cyclic three-carbon π-system. -/

/-- The primitive cube root of unity `ω = exp(2πi/3)`. -/
noncomputable def c3root : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

lemma c3root_pow_three : c3root ^ 3 = 1 := by
  rw [c3root, ← Complex.exp_nat_mul]
  push_cast
  rw [show (3 : ℂ) * (2 * Real.pi * Complex.I / 3) = 2 * Real.pi * Complex.I by ring]
  exact Complex.exp_two_pi_mul_I

lemma c3root_ne_one : c3root ≠ 1 := by
  intro h
  have hre : c3root.re = Real.cos (2 * Real.pi / 3) := by
    rw [c3root, show (2 * (Real.pi : ℂ) * Complex.I / 3)
        = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.exp_ofReal_mul_I_re _
  rw [h] at hre
  have hcos : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show (2 * Real.pi / 3) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
  rw [hcos] at hre
  norm_num at hre

lemma c3root_sum : 1 + c3root + c3root ^ 2 = 0 := by
  have hne : c3root - 1 ≠ 0 := sub_ne_zero.mpr c3root_ne_one
  have hprod : (c3root - 1) * (1 + c3root + c3root ^ 2) = 0 := by
    linear_combination c3root_pow_three
  rcases mul_eq_zero.mp hprod with h | h
  · exact absurd h hne
  · exact h

/-- The adjacency matrix of `C₃`, viewed over `ℂ`. -/
def C3adjC : Matrix (Fin 3) (Fin 3) ℂ := fun i j => if i = j then 0 else 1

/-- The `k`-th Bloch (discrete Fourier) vector `j ↦ ω^{jk}`. -/
noncomputable def c3vec (k : Fin 3) : Fin 3 → ℂ := fun j => c3root ^ ((j : ℕ) * (k : ℕ))

lemma c3vec_ne_zero (k : Fin 3) : c3vec k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [c3vec] at h0

lemma ccos_one : Complex.cos (2 * (Real.pi : ℂ) / 3) = -(1 / 2) := by
  have h : ((Real.cos (2 * Real.pi / 3) : ℝ) : ℂ) = Complex.cos ((2 * Real.pi / 3 : ℝ) : ℂ) :=
    Complex.ofReal_cos _
  rw [show (2 * (Real.pi : ℂ) / 3) = ((2 * Real.pi / 3 : ℝ) : ℂ) by push_cast; ring, ← h,
    show (2 * Real.pi / 3) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]
  push_cast; ring

lemma ccos_two : Complex.cos (2 * (Real.pi : ℂ) * 2 / 3) = -(1 / 2) := by
  have h : ((Real.cos (2 * Real.pi * 2 / 3) : ℝ) : ℂ)
      = Complex.cos ((2 * Real.pi * 2 / 3 : ℝ) : ℂ) := Complex.ofReal_cos _
  rw [show (2 * (Real.pi : ℂ) * 2 / 3) = ((2 * Real.pi * 2 / 3 : ℝ) : ℂ) by push_cast; ring, ← h,
    show (2 * Real.pi * 2 / 3) = Real.pi + Real.pi / 3 by ring, Real.cos_add,
    Real.cos_pi_div_three, Real.sin_pi, Real.cos_pi]
  push_cast; ring

/-- **Explicit Hückel eigenvectors of `C₃`.** For each `k ∈ {0, 1, 2}` the Bloch vector
`c3vec k` is a nonzero eigenvector of the `C₃` adjacency matrix with eigenvalue
`2 * cos (2πk/3)`. -/
theorem huckel_C3_eigenvector (k : Fin 3) :
    c3vec k ≠ 0 ∧
      C3adjC.mulVec (c3vec k)
        = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 3) : ℝ) : ℂ) • c3vec k := by
  refine ⟨c3vec_ne_zero k, ?_⟩
  have h4 : c3root ^ 4 = c3root := by
    calc c3root ^ 4 = c3root ^ 3 * c3root := by ring
      _ = c3root := by rw [c3root_pow_three]; ring
  funext j
  fin_cases k <;> fin_cases j <;>
    simp [Matrix.mulVec, Fin.sum_univ_three, C3adjC, c3vec, dotProduct, ccos_one, ccos_two,
      h4] <;>
    first
      | linear_combination c3root_sum
      | norm_num

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

