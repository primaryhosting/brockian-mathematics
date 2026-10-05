import Mathlib

/-!
# D Ocagne
Category: Fibonacci
Target: Fibonacci.dOcagne
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

/-- The addition form of d'Ocagne's identity, free of subtraction:
`fib (m + n + 1) = fib (m+1) * fib (n+1) + fib m * fib n`. -/
theorem dOcagne_add (m n : ℕ) :
    (Nat.fib (m + n + 1) : ℤ) = Nat.fib (m + 1) * Nat.fib (n + 1) + Nat.fib m * Nat.fib n := by
  rw [Nat.fib_add]
  push_cast
  ring

/-- Auxiliary shifted form of d'Ocagne's identity: with `m = n + k`,
`fib (n+k) * fib (n+1) - fib (n+k+1) * fib n = (-1)^n * fib k`. -/
theorem dOcagne_aux (k n : ℕ) :
    (Nat.fib (n + k) : ℤ) * Nat.fib (n + 1) - (Nat.fib (n + k + 1) : ℤ) * Nat.fib n
      = (-1) ^ n * Nat.fib k := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      have h2 : Nat.fib (n + k + 2) = Nat.fib (n + k) + Nat.fib (n + k + 1) := Nat.fib_add_two
      have e1 : n + 1 + k = n + k + 1 := by ring
      have e2 : n + 1 + 1 = n + 2 := by ring
      have e3 : n + k + 1 + 1 = n + k + 2 := by ring
      rw [e1, e2, e3, h1, h2, pow_succ]
      push_cast
      linear_combination -ih

/-- **d'Ocagne's identity**: for `m ≥ n`,
`fib m * fib (n+1) - fib (m+1) * fib n = (-1)^n * fib (m - n)`. -/
theorem dOcagne (m n : ℕ) (h : n ≤ m) :
    (Nat.fib m : ℤ) * Nat.fib (n + 1) - (Nat.fib (m + 1) : ℤ) * Nat.fib n
      = (-1) ^ n * Nat.fib (m - n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa using dOcagne_aux k n

end Fibonacci

#print axioms Fibonacci.dOcagne
#print axioms Fibonacci.dOcagne_add

