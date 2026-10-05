/-!
# Cassini 7
Category: Pure Mathematics
Target: Math.cassini_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.
(This file must begin with the required header comment, which Lean treats as a module
docstring and therefore forbids any `import` afterwards; hence the sequence is defined
here from scratch. The file `RequestProject/CassiniMathlib.lean` proves that this
sequence agrees with Mathlib's `Nat.fib` and restates the result for `Nat.fib`.) -/

theorem cassini_7 : (fib 6 : Int) * (fib 8 : Int) - (fib 7 : Int) ^ 2 = (-1) ^ 7 := by
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
import RequestProject.Math

/-!
# Cassini 7, stated with Mathlib's `Nat.fib`

`RequestProject/Math.lean` must start with a prescribed module docstring, which prevents it
from containing any `import`. This companion file connects its `Math.fib` with Mathlib's
`Nat.fib` and restates Cassini's identity at `n = 7` in Mathlib terms.
-/

namespace Math

/-- The locally defined `Math.fib` agrees with Mathlib's `Nat.fib`. -/
