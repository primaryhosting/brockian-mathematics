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

lemma evec_dotProduct_self (A : Matrix n n ℂ) (i : n) :
    star (evec A i) ⬝ᵥ evec A i = 1 := by
  set hB := isHermitian_conjTranspose_mul_self A
  have h := hB.eigenvectorBasis.orthonormal.1 i
  have h2 := EuclideanSpace.inner_eq_star_dotProduct
    (hB.eigenvectorBasis i) (hB.eigenvectorBasis i)
  rw [inner_self_eq_norm_sq_to_K, h] at h2
  rw [evec, dotProduct_comm]
  simp [← h2]

omit [DecidableEq n] in
