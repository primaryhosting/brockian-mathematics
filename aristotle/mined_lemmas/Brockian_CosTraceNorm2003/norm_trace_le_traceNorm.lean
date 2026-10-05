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

theorem norm_trace_le_traceNorm (A : Matrix n n ℂ) : ‖A.trace‖ ≤ traceNorm A := by
  rw [trace_eq_sum_evec_diag A, traceNorm]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => norm_evec_diag_le A i)

omit [DecidableEq n] in
/-- The trace of `Aᴴ * A` is the sum of the squared moduli of the entries of `A`. -/
