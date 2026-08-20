/-!
# Cassini 4
Category: Pure Mathematics
Target: Math.cassini_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
This agrees with Mathlib's `Nat.fib`; see `Math.fib_eq_nat_fib` in `Cassini4Mathlib.lean`.
(It is defined here rather than imported because the required module header comment must be
the very first thing in this file, which precludes an `import` statement.) -/

theorem cassini_4_from_mathlib :
    Int.fib (4 + 1) * Int.fib (4 - 1) - Int.fib 4 ^ 2 = (-1 : ℤ) ^ (4 : ℤ).natAbs :=
  Int.fib_succ_mul_fib_pred_sub_fib_sq 4

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

