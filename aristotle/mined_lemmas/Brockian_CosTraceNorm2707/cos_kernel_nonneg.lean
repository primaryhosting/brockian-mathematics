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

theorem cos_kernel_nonneg {ι : Type*} [Fintype ι] (θ x : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * x j * Real.cos (θ i - θ j) := by
  rw [cos_kernel_quadratic_form]
  positivity

/-- Trace-norm style upper bound: the cosine kernel form is bounded by
`(card ι) * ‖x‖²`, the trace of the kernel matrix times the squared norm. -/
