/-
# Cassini
Category: Fibonacci
Target: Fibonacci.cassini
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Fibonacci

/-- **Cassini's identity** for the Fibonacci numbers, stated over `ℤ` to avoid
truncated subtraction: for every `n : ℕ`,
`fib (n+2) * fib n - fib (n+1) ^ 2 = (-1) ^ (n+1)`.

Equivalently, `fib (n+2) * fib n + 1 = fib (n+1) ^ 2` when `n` is even, and
`fib (n+1) ^ 2 + 1 = fib (n+2) * fib n` when `n` is odd. Proved by induction on `n`. -/
theorem cassini (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * (Nat.fib n) - (Nat.fib (n + 1)) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    have h2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    push_cast [h, h2] at ih ⊢
    ring_nf
    ring_nf at ih
    linarith [ih]

end Fibonacci

