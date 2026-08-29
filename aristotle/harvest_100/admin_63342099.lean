/-
# Mobius Root Sum 1
Category: Pure Mathematics
Target: Math.mobius_root_sum_1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- The sum of the primitive `1`-th roots of unity (in `ℂ`) equals `μ 1 = 1`.

The set of primitive `1`-th roots of unity is `{1}`
(`IsPrimitiveRoot.primitiveRoots_one`), so the sum is `1`, which equals `μ 1`. -/
theorem mobius_root_sum_1 :
    ∑ z ∈ primitiveRoots 1 ℂ, z = (ArithmeticFunction.moebius 1 : ℂ) := by
  rw [IsPrimitiveRoot.primitiveRoots_one]
  simp

end Math

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

