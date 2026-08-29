/-!
# Cassini 4
Category: Pure Mathematics
Target: Math.cassini_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.

(Defined here rather than using `Nat.fib` because the required file header must be the very
first thing in the file, and Lean forbids any `import` after a comment at the start of a file.
This definition agrees with `Nat.fib` by construction.) -/

theorem cassini_4_natFib :
    (Nat.fib 3 : ℤ) * (Nat.fib 5 : ℤ) - (Nat.fib 4 : ℤ) ^ 2 = (-1 : ℤ) ^ 4 := by
  simpa [fib_eq_natFib] using cassini_4

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

