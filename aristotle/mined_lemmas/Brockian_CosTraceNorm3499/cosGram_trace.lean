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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

namespace Brockian

/-- The `n × n` real "cosine Gram" matrix attached to a family of phases `x : Fin n → ℝ`,
with entries `cos (x i - x j)`. -/

lemma cosGram_trace (n : ℕ) (x : Fin n → ℝ) : (cosGram n x).trace = (n : ℝ) := by
  simp [Matrix.trace, Matrix.diag, cosGram]

/-- **Cos Trace Norm 3499.**  For any family of phases `x : Fin n → ℝ`, the trace norm
(the sum of the absolute values of the eigenvalues) of the cosine Gram matrix
`A i j = cos (x i - x j)` is exactly `n`.  In particular the trace norm is bounded by `n`,
this bound being attained. -/
