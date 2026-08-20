import Mathlib

/-!
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The cosine Gram matrix of a family of angles: `C i j = cos (θ i - θ j)`. -/

theorem trace_cosGram (n : ℕ) (θ : Fin n → ℝ) : (cosGram n θ).trace = (n : ℝ) := by
  simp [cosGram, Matrix.trace, Matrix.diag]

/--
**Cos Trace Norm 1279.**

For any family of angles `θ : Fin n → ℝ`, the trace (nuclear) norm of the cosine Gram matrix
`C i j = cos (θ i - θ j)`, i.e. the sum of the absolute values of its (real) eigenvalues,
equals exactly `n`.  Consequently it also satisfies the sharp bound `‖C‖_* ≤ n`.
-/
