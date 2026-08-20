/-
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The cosine Gram matrix of a family of angles `x : Fin n → ℝ`:
`cosGram n x i j = cos (x i - x j)`. -/
noncomputable def cosGram (n : ℕ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (x i - x j)

/-- The `2 × n` matrix whose `i`-th column is the unit vector `(cos (x i), sin (x i))`. -/
noncomputable def cosRows (n : ℕ) (x : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of ![fun i => Real.cos (x i), fun i => Real.sin (x i)]

/-- The cosine Gram matrix is indeed a Gram matrix: `cosGram n x = (cosRows n x)ᴴ * cosRows n x`. -/
theorem cosGram_eq_conjTranspose_mul_self (n : ℕ) (x : Fin n → ℝ) :
    cosGram n x = (Matrix.conjTranspose (cosRows n x)) * cosRows n x := by
  ext i j
  simp [cosGram, cosRows, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_sub]

/-- The cosine Gram matrix is positive semidefinite. -/
theorem cosGram_posSemidef (n : ℕ) (x : Fin n → ℝ) : (cosGram n x).PosSemidef := by
  rw [cosGram_eq_conjTranspose_mul_self]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The trace of the cosine Gram matrix is `n`. -/
theorem cosGram_trace (n : ℕ) (x : Fin n → ℝ) : (cosGram n x).trace = (n : ℝ) := by
  simp [cosGram, Matrix.trace, Matrix.diag]

/-- **Cos Trace Norm 2707.**  For any family of angles `x : Fin n → ℝ`, the cosine Gram
matrix `M i j = cos (x i - x j)` is positive semidefinite, and its trace norm (the sum of
the absolute values of its eigenvalues) equals `n`, its trace. -/
theorem CosTraceNorm2707 (n : ℕ) (x : Fin n → ℝ) :
    ∃ h : (cosGram n x).PosSemidef,
      ∑ i, |h.isHermitian.eigenvalues i| = (n : ℝ) ∧
        ∑ i, |h.isHermitian.eigenvalues i| = (cosGram n x).trace := by
  have h1 : ∀ i, |(cosGram_posSemidef n x).isHermitian.eigenvalues i|
      = (cosGram_posSemidef n x).isHermitian.eigenvalues i := fun i =>
    abs_of_nonneg ((cosGram_posSemidef n x).eigenvalues_nonneg i)
  have h2 := Matrix.IsHermitian.trace_eq_sum_eigenvalues (𝕜 := ℝ)
    (cosGram_posSemidef n x).isHermitian
  have h3 : ∑ i, (cosGram_posSemidef n x).isHermitian.eigenvalues i = (cosGram n x).trace := by
    simpa using h2.symm
  refine ⟨cosGram_posSemidef n x, ?_, ?_⟩
  · simp only [h1, h3, cosGram_trace n x]
  · simp only [h1, h3]

end Brockian

