import Mathlib

/-!
# Cassini
Category: Fibonacci
Target: Fibonacci.cassini
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

/-- **Cassini's identity**: for every natural `n`,
`fib (n+2) * fib n - fib (n+1) ^ 2 = (-1) ^ (n+1)`, stated over `ℤ`. -/
theorem cassini (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * (Nat.fib n) - (Nat.fib (n + 1)) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h3 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    have h2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    have hp : (-1 : ℤ) ^ (k + 2) = -(-1) ^ (k + 1) := by ring
    rw [show k + 1 + 2 = k + 3 from rfl, h3, h2, hp]
    push_cast
    rw [h2] at ih
    push_cast at ih
    linarith [ih]

end Fibonacci

