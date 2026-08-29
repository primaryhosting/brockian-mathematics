/-
# Cassini 8
Category: Pure Mathematics
Target: Math.cassini_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The requested header is reproduced verbatim above as a plain block comment: Lean 4
-- requires `import` lines to precede every command, and `/-! ... -/` is a module
-- docstring command, so it cannot appear before `import Mathlib`.)

import Mathlib

namespace Math

/-- **Cassini's identity** for the Fibonacci numbers, stated over the integers:
`F n * F (n + 2) - F (n + 1) ^ 2 = (-1) ^ (n + 1)`. -/

theorem cassini_8 :
    (Nat.fib 7 : ℤ) * (Nat.fib 9 : ℤ) - (Nat.fib 8 : ℤ) ^ 2 = (-1) ^ 8 := by
  simpa using cassini 7

#print axioms Math.cassini
#print axioms Math.cassini_8

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

