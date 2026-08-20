/-!
# Cassini 3
Category: Pure Mathematics
Target: Math.cassini_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

(This file carries the required header comment as its first token, which Lean only
permits in a file with no `import` lines; the companion file `Cassini3Mathlib.lean`
identifies this function with Mathlib's `Nat.fib` and restates the result.) -/

theorem cassini_3_nat_fib :
    (Nat.fib 2 : ℤ) * (Nat.fib 4 : ℤ) - (Nat.fib 3 : ℤ) ^ 2 = (-1) ^ 3 := by
  norm_num [Nat.fib]

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

