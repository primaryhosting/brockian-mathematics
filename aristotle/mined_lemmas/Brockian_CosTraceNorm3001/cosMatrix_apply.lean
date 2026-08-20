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
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

open Matrix

/-- The "cosine kernel" matrix attached to a family of angles `θ : Fin n → ℝ`:
its `(i, j)` entry is `cos (θ i - θ j)`. -/

lemma cosMatrix_apply (n : ℕ) (θ : Fin n → ℝ) (i j : Fin n) :
    cosMatrix n θ i j = Real.cos (θ i - θ j) := rfl

/-- The cosine kernel matrix is (real) symmetric, hence Hermitian. -/
