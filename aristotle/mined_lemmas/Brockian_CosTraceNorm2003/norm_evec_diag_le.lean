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

lemma norm_evec_diag_le (A : Matrix n n ℂ) (i : n) :
    ‖star (evec A i) ⬝ᵥ (A *ᵥ evec A i)‖ ≤ singularValue A i := by
  have h := norm_dotProduct_le (evec A i) (A *ᵥ evec A i)
  rwa [norm_evec_toLp, norm_mulVec_evec, one_mul] at h

omit [DecidableEq n] in
