/-
# Gcd
Category: Fibonacci
Target: Fibonacci.gcd
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gcd
Category: Fibonacci
Target: Fibonacci.gcd
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Fibonacci

/-- **Fibonacci gcd**: `fib (gcd m n) = gcd (fib m) (fib n)` for all naturals `m n`.
This is exactly Mathlib's `Nat.fib_gcd`. -/
theorem gcd (m n : ℕ) : Nat.fib (Nat.gcd m n) = Nat.gcd (Nat.fib m) (Nat.fib n) :=
  Nat.fib_gcd m n

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

