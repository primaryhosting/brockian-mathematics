/-!
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

open Matrix

/-- The "cosine kernel" matrix attached to a family of angles `x : Fin n → ℝ`:
its `(i, j)` entry is `cos (x i - x j)`. -/

theorem cosGram_trace {n : ℕ} (x : Fin n → ℝ) : (cosGram x).trace = n := by
  simp [Matrix.trace, Matrix.diag, cosGram]

/-- **Cos Trace Norm 1279.**  For every family of angles `x : Fin n → ℝ`, the trace norm
(the sum of the absolute values of the eigenvalues, equivalently the sum of the singular
values) of the cosine kernel matrix `(cos (x i - x j))ᵢⱼ` equals `n`.  This is sharp: the
matrix is positive semidefinite with trace `n`, and it has rank at most `2`. -/
