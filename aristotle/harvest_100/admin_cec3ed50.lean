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

/-- **d'Ocagne's identity**, addition form (avoiding natural subtraction):
`fib (m + n + 1) = fib (m+1) * fib (n+1) + fib m * fib n`. -/
theorem dOcagne (m n : ℕ) :
    (Nat.fib (m + n + 1) : ℤ) = Nat.fib (m + 1) * Nat.fib (n + 1) + Nat.fib m * Nat.fib n := by
  rw [Nat.fib_add]
  push_cast
  ring

/-- Auxiliary shifted form of the signed d'Ocagne identity. -/
theorem dOcagne_aux (n k : ℕ) :
    (Nat.fib (n + k) : ℤ) * Nat.fib (n + 1) - (Nat.fib (n + k + 1) : ℤ) * Nat.fib n
      = (-1) ^ n * Nat.fib k := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      have h2 : Nat.fib (n + k + 2) = Nat.fib (n + k) + Nat.fib (n + k + 1) := Nat.fib_add_two
      have e1 : n + 1 + k = n + k + 1 := by ring
      have e2 : n + k + 1 + 1 = n + k + 2 := by ring
      rw [e1, e2, show n + 1 + 1 = n + 2 from rfl, h1, h2]
      push_cast
      push_cast at ih
      ring_nf
      ring_nf at ih
      linarith [ih]

/-- **d'Ocagne's identity**, signed subtraction form, for `n ≤ m`:
`fib m * fib (n+1) - fib (m+1) * fib n = (-1)^n * fib (m - n)`. -/
theorem dOcagne_sub {m n : ℕ} (h : n ≤ m) :
    (Nat.fib m : ℤ) * Nat.fib (n + 1) - (Nat.fib (m + 1) : ℤ) * Nat.fib n
      = (-1) ^ n * Nat.fib (m - n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have := dOcagne_aux n k
  simpa using this

end Fibonacci

#print axioms Fibonacci.dOcagne
#print axioms Fibonacci.dOcagne_sub

