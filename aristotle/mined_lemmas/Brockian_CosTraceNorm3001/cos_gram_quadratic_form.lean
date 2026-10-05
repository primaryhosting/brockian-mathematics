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

lemma cos_gram_quadratic_form (n : ℕ) (x v : Fin n → ℝ) :
    ∑ i, ∑ j, v i * v j * Real.cos (x i - x j)
      = (∑ i, v i * Real.cos (x i)) ^ 2 + (∑ i, v i * Real.sin (x i)) ^ 2 := by
  simp only [Real.cos_sub, sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The cosine Gram matrix is positive semidefinite. -/
