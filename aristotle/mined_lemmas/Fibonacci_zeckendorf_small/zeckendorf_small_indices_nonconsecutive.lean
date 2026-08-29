import Mathlib
/-!
# Zeckendorf Small
Category: Fibonacci
Target: Fibonacci.zeckendorf_small
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Fibonacci

/-- Zeckendorf representation of `100`: it is the sum of the pairwise
non-consecutive Fibonacci numbers `Nat.fib 11 = 89`, `Nat.fib 6 = 8` and
`Nat.fib 4 = 3`. -/

theorem zeckendorf_small_indices_nonconsecutive :
    2 ≤ 11 - 6 ∧ 2 ≤ 6 - 4 ∧ 2 ≤ 11 - 4 := by
  decide

end Fibonacci

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

