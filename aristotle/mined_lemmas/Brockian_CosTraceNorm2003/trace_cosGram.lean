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

import Mathlib

/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten 1-norm) of a Hermitian real matrix, defined as the sum of the
absolute values of its eigenvalues (and `0` on non-Hermitian matrices). -/

theorem trace_cosGram (w θ : n → ℝ) : (cosGram w θ).trace = ∑ i, (w i) ^ 2 := by
  simp [Matrix.trace, Matrix.diag, cosGram, sq]

/-- **Cos Trace Norm 2003.**  For any weights `w` and phases `θ`, the trace norm of the weighted
cosine Gram matrix `C i j = w i * w j * cos (θ i - θ j)` is exactly `∑ i, (w i)^2`. -/
