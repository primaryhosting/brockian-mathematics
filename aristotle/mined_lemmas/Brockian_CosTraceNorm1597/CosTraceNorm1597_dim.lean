/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

/-- The "cosine kernel" matrix `C i j = cos (x i - x j)` attached to phases `x : Fin n → ℝ`. -/

theorem CosTraceNorm1597_dim (x : Fin 1597 → ℝ) (h : (cosMatrix x).IsHermitian) :
    traceNorm h = 1597 := by
  simpa using (CosTraceNorm1597 x h).2

#print axioms Brockian.CosTraceNorm1597
#print axioms Brockian.CosTraceNorm1597_dim

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

