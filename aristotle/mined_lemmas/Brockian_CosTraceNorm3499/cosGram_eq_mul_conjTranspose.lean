import Mathlib

/-!
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Matrix
open scoped ComplexOrder MatrixOrder

/-- The trace norm (Schatten 1-norm) of a complex square matrix:
the trace of the positive square root of `Aᴴ * A`. -/

theorem cosGram_eq_mul_conjTranspose (n : ℕ) (θ : Fin n → ℝ) :
    cosGram n θ = circlePoints n θ * (circlePoints n θ)ᴴ := by
  ext i j
  simp [cosGram, circlePoints, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_sub,
    Matrix.conjTranspose_apply, Complex.conj_ofReal]
  push_cast
  ring

/-- The cosine Gram matrix is positive semidefinite. -/
