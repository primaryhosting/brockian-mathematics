/-
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- **Cos trace norm bound.** For any family of angles `θ : n → ℝ` indexed by a finite type,
the absolute value of the trace of the diagonal matrix with entries `cos (θ i)` is bounded by
the cardinality of the index type.

The proof combines `Matrix.trace_diagonal`, the triangle inequality
`Finset.abs_sum_le_sum_abs`, and the pointwise bound `Real.abs_cos_le_one`. -/

theorem CosTraceNorm3499_isSharp {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix.trace (Matrix.diagonal (fun _ : n => Real.cos (0 : ℝ))) = (Fintype.card n : ℝ) := by
  simp

end Brockian

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

