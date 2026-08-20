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

private theorem fib_two_mul_add_two (s : ℕ) :
    (Nat.fib (2 * s + 2) : ℤ)
      = 2 * Nat.fib s * Nat.fib (s + 1) + Nat.fib (s + 1) ^ 2 := by
  have h : s + (s + 1) + 1 = 2 * s + 2 := by ring
  have hadd := Nat.fib_add s (s + 1)
  rw [h] at hadd
  have h2 := Nat.fib_add_two (n := s)
  rw [hadd]
  push_cast [h2]
  ring

/-- Catalan's identity, addition form (no natural subtraction):
for all `m r : ℕ`, `F (m + r) ^ 2 - F m * F (m + 2 * r) = (-1) ^ m * F r ^ 2`. -/
