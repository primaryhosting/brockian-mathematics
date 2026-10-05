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

theorem conjStarAlgAut_apply (u : Matrix.unitaryGroup n ℂ) (x : Matrix n n ℂ) :
    (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)) u x
      = (u : Matrix n n ℂ) * x * star (u : Matrix n n ℂ) := by
  simp [Unitary.conjStarAlgAut, Unitary.toUnits]
  rfl

/-- The cosine of a Hermitian matrix, defined by the (finite dimensional) continuous functional
calculus: conjugate the diagonal matrix of the cosines of the eigenvalues by the unitary of
eigenvectors. -/
