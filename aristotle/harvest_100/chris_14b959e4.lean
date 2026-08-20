/-
# Cassini
Category: Fibonacci
Target: Fibonacci.cassini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Fibonacci

/-- Cassini's identity, stated over the integers:
`F (n+2) * F n - F (n+1) ^ 2 = (-1) ^ (n+1)`. -/
theorem cassini (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * (Nat.fib n) - (Nat.fib (n + 1)) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hf : (Nat.fib (k + 3) : ℤ) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_add_two (n := k + 1))
    have hf2 : (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_add_two (n := k))
    rw [show k + 1 + 2 = k + 3 from rfl, show k + 1 + 1 = k + 2 from rfl, hf]
    have hp : ((-1 : ℤ)) ^ (k + 1 + 1) = -((-1 : ℤ) ^ (k + 1)) := by ring
    rw [hp]
    linear_combination -ih - (Nat.fib (k + 2) : ℤ) * hf2

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

