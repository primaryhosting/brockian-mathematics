import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Unfolding of the unitary conjugation star-algebra automorphism used by the matrix
spectral theorem. -/

theorem hermCos_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (hermCos hA).IsHermitian := by
  unfold Matrix.IsHermitian hermCos
  simp [conjTranspose_mul, Matrix.mul_assoc, diagonal_conjTranspose,
    Matrix.star_eq_conjTranspose, Pi.star_def, -Complex.ofReal_cos]

/-- Testing a diagonal matrix against a unitary one: the trace of `W * diagonal d` is a convex-type
combination of the entries of `d`, hence bounded by `∑ i, ‖d i‖`. -/
