/-
# Cassini 14
Category: Pure Mathematics
Target: Math.cassini_14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cassini 14
Category: Pure Mathematics
Target: Math.cassini_14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

/-- **Cassini's identity at n = 14**: `F 13 * F 15 - F 14 ^ 2 = (-1) ^ 14`,
stated over the integers with `Nat.fib`.

A search of this Mathlib version turned up no named Cassini identity for `Nat.fib`, so this
instance is discharged by direct computation: `F 13 = 233`, `F 14 = 377`, `F 15 = 610`, and
`233 * 610 - 377 ^ 2 = 142130 - 142129 = 1 = (-1) ^ 14`. -/
theorem cassini_14 :
    (Nat.fib 13 : ℤ) * (Nat.fib 15 : ℤ) - (Nat.fib 14 : ℤ) ^ 2 = (-1) ^ 14 := by
  norm_num [Nat.fib]

end Math

