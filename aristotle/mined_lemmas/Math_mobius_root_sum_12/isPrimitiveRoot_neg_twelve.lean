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
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ArithmeticFunction

namespace Math

/-- If `z` is a primitive 12-th root of unity, then `z ^ 6 = -1`. -/

lemma isPrimitiveRoot_neg_twelve {z : ℂ} (h : IsPrimitiveRoot z 12) :
    IsPrimitiveRoot (-z) 12 := by
  have h6 : z ^ 6 = -1 := pow_six_eq_neg_one_of_isPrimitiveRoot_twelve h
  have hz7 : z ^ 7 = -z := by
    have : z ^ 7 = z ^ 6 * z := by ring
    rw [this, h6]; ring
  have := h.pow_of_coprime 7 (by decide)
  rwa [hz7] at this

/-- The sum of the primitive 12-th roots of unity equals `μ(12) = 0`. -/
