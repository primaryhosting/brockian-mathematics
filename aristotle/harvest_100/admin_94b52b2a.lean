/-
# Cassini 3
Category: Pure Mathematics
Target: Math.cassini_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cassini 3
Category: Pure Mathematics
Target: Math.cassini_3
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

/-- Cassini's identity in the case `n = 3`:
`F(2) * F(4) - F(3) ^ 2 = (-1) ^ 3`, i.e. `1 * 3 - 2 ^ 2 = -1`.

This is the `n = 3` instance of Cassini's identity `F(n-1)·F(n+1) - F(n)^2 = (-1)^n`.
It is proved by evaluating the relevant Fibonacci numbers `F 2 = 1`, `F 3 = 2`, `F 4 = 3`
from the definition `Nat.fib`. -/
theorem cassini_3 :
    (Nat.fib 2 : ℤ) * (Nat.fib 4 : ℤ) - (Nat.fib 3 : ℤ) ^ 2 = (-1) ^ 3 := by
  norm_num [Nat.fib]

end Math

