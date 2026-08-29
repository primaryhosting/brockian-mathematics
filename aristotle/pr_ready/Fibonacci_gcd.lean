/-!
# Gcd
Category: Fibonacci
Target: Fibonacci.gcd
Statement: Fibonacci-gcd: for all naturals m n, Nat.fib (Nat.gcd m n) = Nat.gcd (Nat.fib m) (Nat.fib n). (Use Mathlib's Nat.fib_gcd.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Fibonacci

/-- For all naturals `m n`, `fib (gcd m n) = gcd (fib m) (fib n)`. -/
theorem gcd (m n : ℕ) : Nat.fib (Nat.gcd m n) = Nat.gcd (Nat.fib m) (Nat.fib n) :=
  Nat.fib_gcd m n

end Fibonacci

