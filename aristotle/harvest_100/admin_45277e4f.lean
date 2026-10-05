/-
# Consecutive Coprime
Category: Fibonacci
Target: Fibonacci.consecutive_coprime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Fibonacci

/-- Consecutive Fibonacci numbers are coprime: `gcd (fib n) (fib (n+1)) = 1`.

This is exactly Mathlib's `Nat.fib_coprime_fib_succ`; an independent induction proof
is given as `Fibonacci.consecutive_coprime'` below. -/
theorem consecutive_coprime (n : ℕ) : Nat.Coprime (Nat.fib n) (Nat.fib (n + 1)) :=
  Nat.fib_coprime_fib_succ n

/-- Self-contained induction proof of the same statement, not relying on
`Nat.fib_coprime_fib_succ`. -/
theorem consecutive_coprime' (n : ℕ) : Nat.Coprime (Nat.fib n) (Nat.fib (n + 1)) := by
  induction n with
  | zero => simp [Nat.Coprime]
  | succ n ih =>
      rw [Nat.fib_add_two, Nat.coprime_add_self_right]
      exact ih.symm

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

