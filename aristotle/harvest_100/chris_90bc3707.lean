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

/-!
# Cassini
Category: Fibonacci
Target: Fibonacci.cassini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Fibonacci

/-- Cassini's identity, stated over the integers:
`fib (n+2) * fib n - fib (n+1) ^ 2 = (-1) ^ (n+1)`. -/
theorem cassini (n : Nat) :
    (Nat.fib (n + 2) : Int) * (Nat.fib n) - (Nat.fib (n + 1)) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have h2 : (Nat.fib (k + 2) : Int) = Nat.fib k + Nat.fib (k + 1) := by
        rw [Nat.fib_add_two]; push_cast; ring
      have h3 : (Nat.fib (k + 3) : Int) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
        rw [show k + 3 = (k + 1) + 2 from rfl, Nat.fib_add_two]; push_cast; ring
      rw [show k + 1 + 2 = k + 3 from rfl, h3, h2, pow_succ]
      rw [show k + 1 + 1 = k + 2 from rfl, h2] at ih
      linear_combination -ih

end Fibonacci

