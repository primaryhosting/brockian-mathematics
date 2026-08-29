import Mathlib

/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped MatrixOrder

namespace Brockian

open Matrix

/-- The *cosine Gram matrix* of a family of phases `θ : Fin n → ℝ`:
its `(i, j)` entry is `cos (θ i - θ j)`. -/

theorem cosGram_eq_conjTranspose_mul_self {n : ℕ} (θ : Fin n → ℝ) :
    cosGram θ = (phaseVectors θ)ᴴ * phaseVectors θ := by
  ext i j
  simp only [cosGram, phaseVectors, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, star_trivial]
  rw [Fin.sum_univ_two]
  simp [Real.cos_sub]

/-- The cosine Gram matrix is positive semidefinite. -/
