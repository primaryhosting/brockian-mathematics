/-
# D Ocagne
Category: Fibonacci
Target: Fibonacci.dOcagne
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

/-- **d'Ocagne's identity**, stated in addition form to avoid natural subtraction:
`fib (m + n + 1) = fib (m + 1) * fib (n + 1) + fib m * fib n`.
This is `Nat.fib_add` up to commutativity of addition and multiplication. -/

theorem dOcagne_shift (n k : ℕ) :
    (Nat.fib (n + k) : ℤ) * Nat.fib (n + 1) - (Nat.fib (n + k + 1) : ℤ) * Nat.fib n
      = (-1) ^ n * Nat.fib k := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : Nat.fib (n + 1 + 1) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      have h2 : Nat.fib (n + k + 1 + 1) = Nat.fib (n + k) + Nat.fib (n + k + 1) :=
        Nat.fib_add_two
      have e1 : n + 1 + k = n + k + 1 := by ring
      rw [e1, h1, h2, show ((-1 : ℤ)) ^ (n + 1) = -(-1) ^ n by ring]
      push_cast
      nlinarith [ih]

/-- **d'Ocagne's identity** in its classical subtractive form: for `m ≥ n`,
`fib m * fib (n + 1) - fib (m + 1) * fib n = (-1)^n * fib (m - n)`. -/
