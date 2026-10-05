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

lemma dotProduct_conjTranspose_mul (A : Matrix n n ℂ) (v : n → ℂ) :
    star (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = star v ⬝ᵥ ((Aᴴ * A) *ᵥ v) := by
  rw [star_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec,
    mulVec_mulVec]

