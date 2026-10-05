import Mathlib

/-!
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian

/-- **Cosine trace-norm bound.**
For any family of angles `f : Fin n → ℝ`, the trace of the diagonal matrix whose
entries are `cos (f i)` has norm at most `n`.

The proof only uses `Matrix.trace_diagonal`, the triangle inequality for finite sums
(`Finset.abs_sum_le_sum_abs`) and `Real.abs_cos_le_one`. -/

theorem CosTraceNorm3499_dim (f : Fin 3499 → ℝ) :
    ‖Matrix.trace (Matrix.diagonal fun i => Real.cos (f i))‖ ≤ 3499 := by
  simpa using CosTraceNorm3499 f

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

