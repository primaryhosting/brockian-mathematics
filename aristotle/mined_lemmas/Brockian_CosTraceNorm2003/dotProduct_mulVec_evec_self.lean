/-
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
open scoped ComplexOrder

namespace Brockian

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `i`-th singular value of a complex square matrix `A`: the square root of the `i`-th
eigenvalue of the positive semidefinite matrix `Aᴴ * A`. -/

lemma dotProduct_mulVec_evec_self (A : Matrix n n ℂ) (i : n) :
    star (A *ᵥ evec A i) ⬝ᵥ (A *ᵥ evec A i) = ((singularValue A i ^ 2 : ℝ) : ℂ) := by
  rw [dotProduct_conjTranspose_mul, evec,
    (isHermitian_conjTranspose_mul_self A).mulVec_eigenvectorBasis i,
    dotProduct_smul, ← evec, evec_dotProduct_self, singularValue_sq]
  simp

/-- The Euclidean norm of `A` applied to the `i`-th eigenvector of `Aᴴ A` is the `i`-th singular
value of `A`. -/
