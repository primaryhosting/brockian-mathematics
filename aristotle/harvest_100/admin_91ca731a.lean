/-
# Mobius Root Sum 1
Category: Pure Mathematics
Target: Math.mobius_root_sum_1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 1
Category: Pure Mathematics
Target: Math.mobius_root_sum_1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The set of primitive `1`-st roots of unity in `ℂ` is `{1}`. -/
theorem primitiveRoots_one_complex : primitiveRoots 1 ℂ = {1} := by
  ext x
  simp

/-- The sum of the primitive `1`-st roots of unity in `ℂ` equals `μ(1) = 1`. -/
theorem mobius_root_sum_1 :
    ∑ z ∈ primitiveRoots 1 ℂ, z = (ArithmeticFunction.moebius 1 : ℤ) := by
  rw [primitiveRoots_one_complex]
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

