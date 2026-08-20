/-!
# Cassini 9
Category: Pure Mathematics
Target: Math.cassini_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, valued in `ℤ`: `fibZ 0 = 0`, `fibZ 1 = 1`,
`fibZ (n + 2) = fibZ n + fibZ (n + 1)`. -/

theorem cassini_9 : fibZ 8 * fibZ 10 - fibZ 9 ^ 2 = (-1) ^ 9 := by
  decide

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

import Mathlib
import RequestProject.Cassini9

/-!
# Cassini 9, restated with Mathlib's `Nat.fib`

The main statement `Math.cassini_9` lives in `RequestProject/Cassini9.lean` and is
phrased with the self-contained integer Fibonacci sequence `Math.fibZ`.  Here we
check that `Math.fibZ` agrees with Mathlib's `Nat.fib`, and restate Cassini's
identity at `n = 9` in those terms.
-/

namespace Math

/-- `Math.fibZ` is the integer cast of Mathlib's `Nat.fib`. -/
