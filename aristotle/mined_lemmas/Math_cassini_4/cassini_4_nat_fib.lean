/-!
# Cassini 4
Category: Pure Mathematics
Target: Math.cassini_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean requires all `import` commands to precede any other command, including
module doc comments.  Since the requested header must be the very first thing in
this file, the file is kept self-contained (no imports beyond the core prelude)
and the Fibonacci sequence is defined directly below with the standard recursion,
matching `Nat.fib` (`F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`).
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`. -/

theorem cassini_4_nat_fib :
    (Nat.fib 3 : ℤ) * (Nat.fib 5 : ℤ) - (Nat.fib 4 : ℤ) ^ 2 = (-1) ^ 4 := by
  simpa [fib_eq_nat_fib] using cassini_4

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

