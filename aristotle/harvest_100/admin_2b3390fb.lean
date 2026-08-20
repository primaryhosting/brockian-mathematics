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
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

open Matrix

/-- The "cosine kernel" matrix attached to a family of angles `θ : Fin n → ℝ`:
its `(i, j)` entry is `cos (θ i - θ j)`. -/
noncomputable def cosMatrix (n : ℕ) (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (θ i - θ j)

lemma cosMatrix_apply (n : ℕ) (θ : Fin n → ℝ) (i j : Fin n) :
    cosMatrix n θ i j = Real.cos (θ i - θ j) := rfl

/-- The cosine kernel matrix is (real) symmetric, hence Hermitian. -/
lemma cosMatrix_isHermitian (n : ℕ) (θ : Fin n → ℝ) : (cosMatrix n θ).IsHermitian := by
  ext i j
  simp [cosMatrix, Matrix.conjTranspose_apply, ← Real.cos_neg (θ i - θ j)]

/-- The quadratic form of the cosine kernel matrix is a sum of two squares. -/
lemma cosMatrix_quadratic_form (n : ℕ) (θ : Fin n → ℝ) (x : Fin n → ℝ) :
    star x ⬝ᵥ (cosMatrix n θ *ᵥ x)
      = (∑ i, x i * Real.cos (θ i)) ^ 2 + (∑ i, x i * Real.sin (θ i)) ^ 2 := by
  have h1 : ((∑ i, x i * Real.cos (θ i)) ^ 2 : ℝ)
      = ∑ i, ∑ j, (x i * Real.cos (θ i)) * (x j * Real.cos (θ j)) := by
    rw [sq, Finset.sum_mul_sum]
  have h2 : ((∑ i, x i * Real.sin (θ i)) ^ 2 : ℝ)
      = ∑ i, ∑ j, (x i * Real.sin (θ i)) * (x j * Real.sin (θ j)) := by
    rw [sq, Finset.sum_mul_sum]
  rw [h1, h2, ← Finset.sum_add_distrib]
  simp only [dotProduct, Matrix.mulVec, cosMatrix, Matrix.of_apply, Pi.star_apply,
    star_trivial, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Real.cos_sub]
  ring

/-- The cosine kernel matrix is positive semidefinite. -/
lemma cosMatrix_posSemidef (n : ℕ) (θ : Fin n → ℝ) : (cosMatrix n θ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨cosMatrix_isHermitian n θ, fun x => ?_⟩
  rw [cosMatrix_quadratic_form]
  positivity

/-- The trace of the cosine kernel matrix is `n`. -/
lemma cosMatrix_trace (n : ℕ) (θ : Fin n → ℝ) : (cosMatrix n θ).trace = n := by
  simp [Matrix.trace, Matrix.diag, cosMatrix]

/-- **Cos Trace Norm 3001.**  For any family of angles `θ : Fin n → ℝ`, the trace norm
(the sum of the absolute values of the eigenvalues, i.e. the Schatten-1 norm) of the
cosine kernel matrix `(cos (θ i - θ j))` at position `(i, j)` is exactly `n`.  Equivalently, the matrix is
positive semidefinite with trace `n`. -/
theorem CosTraceNorm3001 (n : ℕ) (θ : Fin n → ℝ) :
    ∑ i, |(cosMatrix_isHermitian n θ).eigenvalues i| = (n : ℝ) := by
  have hpos : ∀ i, 0 ≤ (cosMatrix_isHermitian n θ).eigenvalues i := fun i =>
    (cosMatrix_posSemidef n θ).eigenvalues_nonneg i
  have habs : ∑ i, |(cosMatrix_isHermitian n θ).eigenvalues i|
      = ∑ i, (cosMatrix_isHermitian n θ).eigenvalues i :=
    Finset.sum_congr rfl fun i _ => abs_of_nonneg (hpos i)
  have ht := (cosMatrix_isHermitian n θ).trace_eq_sum_eigenvalues (𝕜 := ℝ)
  rw [cosMatrix_trace] at ht
  rw [habs]
  simpa using ht.symm

end Brockian

