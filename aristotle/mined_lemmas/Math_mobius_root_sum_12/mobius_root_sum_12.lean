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

/-
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- If `ζ` is a primitive 12-th root of unity in `ℂ`, then so is `-ζ`
(indeed `-ζ = ζ ^ 7` and `gcd 7 12 = 1`). -/

theorem mobius_root_sum_12 :
    ∑ z ∈ primitiveRoots 12 ℂ, z = (ArithmeticFunction.moebius 12 : ℂ) := by
  have hmu : ArithmeticFunction.moebius 12 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  rw [hmu]
  push_cast
  refine Finset.sum_involution (fun a _ => -a) ?_ ?_ ?_ ?_
  · intro a _; ring
  · intro a _ hne h
    apply hne
    have h2 : (2 : ℂ) * a = 0 := by linear_combination -h
    simpa using h2
  · intro a ha
    rw [mem_primitiveRoots (by norm_num)] at ha
    rw [mem_primitiveRoots (by norm_num : 0 < 12)]
    exact neg_isPrimitiveRoot_twelve ha
  · intro a _; ring

end Math

