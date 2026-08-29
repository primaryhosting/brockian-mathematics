/-
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
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

/-- The quadratic form of the cosine kernel `cos (θ i - θ j)` is a sum of two squares. -/

theorem cos_kernel_quadratic_form {ι : Type*} [Fintype ι] (θ x : ι → ℝ) :
    ∑ i, ∑ j, x i * x j * Real.cos (θ i - θ j)
      = (∑ i, x i * Real.cos (θ i)) ^ 2 + (∑ i, x i * Real.sin (θ i)) ^ 2 := by
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.cos_sub]
  ring

/-- The cosine kernel matrix `A i j = cos (θ i - θ j)` is positive semidefinite as a real
quadratic form. -/
