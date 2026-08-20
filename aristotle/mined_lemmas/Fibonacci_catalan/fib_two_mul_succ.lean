/-
# Catalan
Category: Fibonacci
Target: Fibonacci.catalan
Verification: pending
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

/-- Cassini's identity: `F (n+1) ^ 2 - F n * F (n+2) = (-1) ^ n`. -/

private theorem fib_two_mul_succ (s : ℕ) :
    (Nat.fib (2 * s + 1) : ℤ) = Nat.fib (s + 1) ^ 2 + Nat.fib s ^ 2 := by
  rw [Nat.fib_two_mul_add_one]; push_cast; ring

/-- Value of `F (2 s + 2)` in terms of `F s` and `F (s+1)`. -/
