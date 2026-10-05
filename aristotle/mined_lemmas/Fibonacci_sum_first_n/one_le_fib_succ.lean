import Mathlib

/-!
# Sum First N
Category: Fibonacci
Target: Fibonacci.sum_first_n
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Fibonacci

/-- `Nat.fib (n+1)` is always at least `1`. -/

theorem one_le_fib_succ (n : ℕ) : 1 ≤ Nat.fib (n + 1) :=
  Nat.fib_pos.mpr n.succ_pos

/-- The sum of the first `n` Fibonacci numbers is `Nat.fib (n+1) - 1`. -/
