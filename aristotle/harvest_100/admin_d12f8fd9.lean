/-
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
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

/-- The cosine Gram matrix of a family of angles: `C i j = cos (θ i - θ j)`. -/
noncomputable def cosGram {n : ℕ} (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (θ i - θ j)

/-- The `2 × n` matrix whose columns are the unit vectors `(cos θ j, sin θ j)`. -/
noncomputable def cosSinRows {n : ℕ} (θ : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of fun k j => if k = 0 then Real.cos (θ j) else Real.sin (θ j)

/-- The cosine Gram matrix is the Gram matrix of the unit vectors `(cos θ j, sin θ j)`. -/
lemma cosGram_eq_conjTranspose_mul_self {n : ℕ} (θ : Fin n → ℝ) :
    cosGram θ = (cosSinRows θ)ᴴ * (cosSinRows θ) := by
  ext i j
  simp only [cosGram, cosSinRows, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    star_trivial, Fin.sum_univ_two]
  simp [Real.cos_sub]

/-- The cosine Gram matrix is positive semidefinite. -/
lemma cosGram_posSemidef {n : ℕ} (θ : Fin n → ℝ) : (cosGram θ).PosSemidef := by
  rw [cosGram_eq_conjTranspose_mul_self]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The cosine Gram matrix is symmetric. -/
lemma cosGram_isHermitian {n : ℕ} (θ : Fin n → ℝ) : (cosGram θ).IsHermitian :=
  (cosGram_posSemidef θ).isHermitian

/-- The trace of the cosine Gram matrix is `n`. -/
lemma cosGram_trace {n : ℕ} (θ : Fin n → ℝ) : (cosGram θ).trace = (n : ℝ) := by
  simp [Matrix.trace, Matrix.diag, cosGram]

/-- **Trace-norm bound for the cosine Gram matrix.**

For any angles `θ : Fin n → ℝ`, the matrix `C i j = cos (θ i - θ j)` is symmetric positive
semidefinite, and its trace norm (the sum of the absolute values of its eigenvalues, i.e. the
sum of its singular values) is exactly `n`; in particular it is bounded by `n`. -/
theorem CosTraceNorm3499 {n : ℕ} (θ : Fin n → ℝ) :
    ∑ i, |(cosGram_isHermitian θ).eigenvalues i| = (n : ℝ) ∧
      ∑ i, |(cosGram_isHermitian θ).eigenvalues i| ≤ (n : ℝ) := by
  have habs : ∀ i, |(cosGram_isHermitian θ).eigenvalues i|
      = (cosGram_isHermitian θ).eigenvalues i := fun i =>
    abs_of_nonneg ((cosGram_posSemidef θ).eigenvalues_nonneg i)
  have hsum : ∑ i, |(cosGram_isHermitian θ).eigenvalues i| = (n : ℝ) := by
    calc ∑ i, |(cosGram_isHermitian θ).eigenvalues i|
        = ∑ i, (cosGram_isHermitian θ).eigenvalues i := by
          exact Finset.sum_congr rfl fun i _ => habs i
      _ = (cosGram θ).trace := ((cosGram_isHermitian θ).trace_eq_sum_eigenvalues).symm
      _ = (n : ℝ) := cosGram_trace θ
  exact ⟨hsum, le_of_eq hsum⟩

end Brockian

