/-
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

open Matrix

/-- The quadratic form of the cosine Gram matrix `cos (x i - x j)` is a sum of two squares. -/
lemma cos_gram_quadratic_form (n : ℕ) (x v : Fin n → ℝ) :
    ∑ i, ∑ j, v i * v j * Real.cos (x i - x j)
      = (∑ i, v i * Real.cos (x i)) ^ 2 + (∑ i, v i * Real.sin (x i)) ^ 2 := by
  simp only [Real.cos_sub, sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The cosine Gram matrix is positive semidefinite. -/
lemma cos_gram_posSemidef (n : ℕ) (x : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, M i j = Real.cos (x i - x j)) :
    M.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, hM]
    rw [show x j - x i = -(x i - x j) by ring, Real.cos_neg]
  · intro v
    have h : star v ⬝ᵥ (M *ᵥ v) = ∑ i, ∑ j, v i * v j * Real.cos (x i - x j) := by
      simp only [dotProduct, mulVec, star_trivial, Pi.star_apply, Finset.mul_sum, hM]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [h, cos_gram_quadratic_form n x v]
    positivity

/-- The trace of the cosine Gram matrix is `n`. -/
lemma cos_gram_trace (n : ℕ) (x : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, M i j = Real.cos (x i - x j)) :
    Matrix.trace M = (n : ℝ) := by
  simp [Matrix.trace, Matrix.diag, hM]

/-- The quadratic form of the cosine Gram matrix is bounded by `n ‖v‖²`. -/
lemma cos_gram_quadratic_form_le (n : ℕ) (x v : Fin n → ℝ) :
    ∑ i, ∑ j, v i * v j * Real.cos (x i - x j) ≤ (n : ℝ) * ∑ i, v i ^ 2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (fun i => Real.cos (x i))
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (fun i => Real.sin (x i))
  have hsum : (∑ i, Real.cos (x i) ^ 2) + (∑ i, Real.sin (x i) ^ 2) = (n : ℝ) := by
    rw [← Finset.sum_add_distrib]
    simp [Real.cos_sq_add_sin_sq]
  rw [cos_gram_quadratic_form n x v]
  calc (∑ i, v i * Real.cos (x i)) ^ 2 + (∑ i, v i * Real.sin (x i)) ^ 2
      ≤ (∑ i, v i ^ 2) * (∑ i, Real.cos (x i) ^ 2) + (∑ i, v i ^ 2) * (∑ i, Real.sin (x i) ^ 2) :=
        add_le_add hc hs
    _ = (n : ℝ) * ∑ i, v i ^ 2 := by rw [← mul_add, hsum]; ring

/-- **Cos Trace Norm 3001.**
For any phases `x : Fin n → ℝ`, the cosine Gram matrix `M i j = cos (x i - x j)` is positive
semidefinite, its trace norm (the sum of the absolute values of its eigenvalues) equals `n`,
and its quadratic form obeys the sharp bound `vᵀ M v ≤ n ‖v‖²`. -/
theorem CosTraceNorm3001 (n : ℕ) (x : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, M i j = Real.cos (x i - x j))
    (hHerm : M.IsHermitian) :
    M.PosSemidef ∧
      (∑ i, |hHerm.eigenvalues i| = (n : ℝ)) ∧
      (∀ v : Fin n → ℝ, ∑ i, ∑ j, v i * v j * Real.cos (x i - x j) ≤ (n : ℝ) * ∑ i, v i ^ 2) := by
  refine ⟨cos_gram_posSemidef n x M hM, ?_, cos_gram_quadratic_form_le n x⟩
  have hpsd : M.PosSemidef := cos_gram_posSemidef n x M hM
  have habs : ∀ i, |hHerm.eigenvalues i| = hHerm.eigenvalues i := fun i =>
    abs_of_nonneg (hpsd.eigenvalues_nonneg i)
  calc ∑ i, |hHerm.eigenvalues i| = ∑ i, hHerm.eigenvalues i := by
        exact Finset.sum_congr rfl fun i _ => habs i
    _ = Matrix.trace M := by
        have := hHerm.trace_eq_sum_eigenvalues
        simpa using this.symm
    _ = (n : ℝ) := cos_gram_trace n x M hM

end Brockian

