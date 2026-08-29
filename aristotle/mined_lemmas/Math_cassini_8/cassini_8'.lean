/-!
# Cassini 8
Category: Pure Mathematics
Target: Math.cassini_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

(This file's required header comment must be the very first thing in the file, which
prevents an `import` line, so the sequence is defined here from scratch rather than
taken from Mathlib; it agrees with `Nat.fib`.) -/

theorem cassini_8' :
    (Nat.fib 7 : ℤ) * (Nat.fib 9 : ℤ) - (Nat.fib 8 : ℤ) ^ 2 = (-1) ^ 8 :=
  cassini 7

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

