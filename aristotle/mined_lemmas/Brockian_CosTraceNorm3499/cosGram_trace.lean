/-
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
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

/-- The cosine Gram matrix of a family of angles: `C i j = cos (θ i - θ j)`. -/

lemma cosGram_trace {n : ℕ} (θ : Fin n → ℝ) : (cosGram θ).trace = (n : ℝ) := by
  simp [Matrix.trace, Matrix.diag, cosGram]

/-- **Trace-norm bound for the cosine Gram matrix.**

For any angles `θ : Fin n → ℝ`, the matrix `C i j = cos (θ i - θ j)` is symmetric positive
semidefinite, and its trace norm (the sum of the absolute values of its eigenvalues, i.e. the
sum of its singular values) is exactly `n`; in particular it is bounded by `n`. -/
