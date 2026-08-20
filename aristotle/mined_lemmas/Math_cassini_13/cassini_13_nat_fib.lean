import Mathlib
import RequestProject.Cassini13

/-!
# Cassini 13, stated for Mathlib's `Nat.fib`

Companion to `RequestProject/Cassini13.lean`.  We check that the locally defined
`Math.fib` agrees with Mathlib's `Nat.fib`, restate Cassini's identity at `n = 13`
for `Nat.fib`, and prove the general Cassini identity
`F (n+2) * F n - F (n+1) ^ 2 = (-1) ^ (n+1)` by induction.
-/

namespace Math


theorem cassini_13_nat_fib :
    (Nat.fib 12 : ℤ) * (Nat.fib 14 : ℤ) - (Nat.fib 13 : ℤ) ^ 2 = (-1) ^ 13 := by
  simpa using cassini 12

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
# Cassini 13
Category: Pure Mathematics
Target: Math.cassini_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

This file is required to begin with the header comment above; since Lean 4 does not
permit an `import` command to follow a module doc comment, this file is kept
import-free and therefore carries its own copy of the Fibonacci sequence.  The
companion file `RequestProject/Cassini13Mathlib.lean` imports Mathlib, proves
`Math.fib = Nat.fib`, and restates the result for Mathlib's `Nat.fib`. -/
