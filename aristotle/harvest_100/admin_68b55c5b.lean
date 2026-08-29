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

/-- **Cassini's identity**, stated over the integers to avoid truncated subtraction:
for every natural `n`, `fib (n+2) * fib n - fib (n+1) ^ 2 = (-1) ^ (n+1)`. -/
theorem cassini (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * (Nat.fib n : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : (Nat.fib (n + 3) : ℤ) = (Nat.fib (n + 2) : ℤ) + (Nat.fib (n + 1) : ℤ) := by
        have h1n : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
        push_cast [h1n]
        ring
      have h2 : (Nat.fib (n + 2) : ℤ) = (Nat.fib (n + 1) : ℤ) + (Nat.fib n : ℤ) := by
        have h2n : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
        push_cast [h2n]
        ring
      rw [show n + 1 + 2 = n + 3 from rfl, h1]
      have hpow : (-1 : ℤ) ^ (n + 1 + 1) = -((-1 : ℤ) ^ (n + 1)) := by
        rw [pow_succ]; ring
      rw [hpow, ← ih]
      linear_combination (-(Nat.fib (n + 2) : ℤ)) * h2

end Fibonacci

