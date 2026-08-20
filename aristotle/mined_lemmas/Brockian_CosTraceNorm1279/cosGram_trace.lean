/-
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The trace norm (Schatten 1-norm) of a real Hermitian (i.e. symmetric) matrix:
the sum of the absolute values of its eigenvalues. -/

lemma cosGram_trace (n : ℕ) (θ : Fin n → ℝ) : (cosGram n θ).trace = (n : ℝ) := by
  simp [Matrix.trace, Matrix.diag, cosGram]

/-- **Cos Trace Norm 1279.**  The trace norm of the `n × n` cosine Gram matrix
`(i, j) ↦ cos (θ i - θ j)` equals `n`, for any family of angles `θ`. -/
