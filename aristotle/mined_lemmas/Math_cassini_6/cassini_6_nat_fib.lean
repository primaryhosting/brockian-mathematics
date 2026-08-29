import Mathlib
import RequestProject.Cassini6

/-!
# Cassini 6 — agreement with Mathlib's Fibonacci numbers

The target file `RequestProject/Cassini6.lean` must literally begin with a module
documentation comment, so it cannot contain any `import`.  It therefore defines the
Fibonacci sequence `Math.fib` from scratch.  Here we check that this definition
agrees with Mathlib's `Nat.fib`, and restate Cassini's identity at `n = 6` in terms
of `Nat.fib`.
-/

namespace Math

/-- The locally defined `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem cassini_6_nat_fib :
    (Nat.fib 5 : ℤ) * (Nat.fib 7 : ℤ) - (Nat.fib 6 : ℤ) ^ 2 = (-1) ^ 6 := by
  simpa [fib_eq_nat_fib] using cassini_6

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

/-!
# Cassini 6
Category: Pure Mathematics
Target: Math.cassini_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/
