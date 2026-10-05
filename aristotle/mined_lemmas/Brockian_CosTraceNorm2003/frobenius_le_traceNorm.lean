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

theorem frobenius_le_traceNorm (A : Matrix n n ℂ) :
    Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) ≤ traceNorm A := by
  rw [← sum_singularValue_sq]
  exact (Real.sqrt_le_left (traceNorm_nonneg A)).mpr
    (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => singularValue_nonneg A i)

/-- Sanity check: the trace norm of the `1 × 1` matrix `(z)` is `‖z‖`. -/
