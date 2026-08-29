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

theorem hermCos_zero : hermCos (A := (0 : Matrix n n ℂ)) Matrix.isHermitian_zero = 1 := by
  have h1 : (star (Matrix.isHermitian_zero (n := n) (α := ℂ)).eigenvectorUnitary.val) *
      ((Matrix.isHermitian_zero (n := n) (α := ℂ)).eigenvectorUnitary.val) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 (Matrix.isHermitian_zero (n := n) (α := ℂ)).eigenvectorUnitary.2
  have h2 : (Matrix.isHermitian_zero (n := n) (α := ℂ)).eigenvectorUnitary.val *
      star ((Matrix.isHermitian_zero (n := n) (α := ℂ)).eigenvectorUnitary.val) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 (Matrix.isHermitian_zero (n := n) (α := ℂ)).eigenvectorUnitary.2
  simp only [hermCos, eigenvalues_zero_eq_zero, Real.cos_zero, Complex.ofReal_one,
    Matrix.diagonal_one, Matrix.mul_one, h2]

/-- Sharpness of `CosTraceNorm4001`: the trace-norm bound `card n` is attained at `A = 0`. -/
