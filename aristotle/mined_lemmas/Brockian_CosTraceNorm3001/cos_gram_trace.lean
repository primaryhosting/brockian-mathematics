/-
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

open Matrix

/-- The quadratic form of the cosine Gram matrix `cos (x i - x j)` is a sum of two squares. -/

lemma cos_gram_trace (n : ℕ) (x : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, M i j = Real.cos (x i - x j)) :
    Matrix.trace M = (n : ℝ) := by
  simp [Matrix.trace, Matrix.diag, hM]

/-- The quadratic form of the cosine Gram matrix is bounded by `n ‖v‖²`. -/
