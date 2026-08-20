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

/-- d'Ocagne's identity, stated in additive form (avoiding natural subtraction):
`F (m + n + 1) = F (m+1) * F (n+1) + F m * F n`.
This follows directly from Mathlib's `Nat.fib_add`. -/
theorem dOcagne (m n : ℕ) :
    (Nat.fib (m + n + 1) : ℤ) = Nat.fib (m + 1) * Nat.fib (n + 1) + Nat.fib m * Nat.fib n := by
  rw [Nat.fib_add m n]
  push_cast
  ring

/-- Auxiliary form of d'Ocagne's identity with the difference `m - n` replaced by `k`
(i.e. `m = n + k`):
`F (n + k) * F (n + 1) - F (n + k + 1) * F n = (-1)^n * F k`. -/
theorem dOcagne_sub_aux (n k : ℕ) :
    (Nat.fib (n + k) : ℤ) * Nat.fib (n + 1) - (Nat.fib (n + k + 1) : ℤ) * Nat.fib n
      = (-1) ^ n * Nat.fib k := by
  induction n with
  | zero => simp
  | succ n ih =>
      have e1 : n + 1 + k = n + k + 1 := by omega
      have e2 : n + 1 + k + 1 = (n + k) + 2 := by omega
      have h2 : (Nat.fib ((n + k) + 2) : ℤ) = Nat.fib (n + k) + Nat.fib (n + k + 1) := by
        rw [Nat.fib_add_two]; push_cast; ring
      have h3 : (Nat.fib (n + 1 + 1) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
        rw [Nat.fib_add_two]; push_cast; ring
      rw [e2, e1, h2, h3, pow_succ]
      linear_combination -ih

/-- d'Ocagne's identity in its classical subtractive form, for `n ≤ m`:
`F m * F (n+1) - F (m+1) * F n = (-1)^n * F (m - n)`. -/
theorem dOcagne_sub {m n : ℕ} (h : n ≤ m) :
    (Nat.fib m : ℤ) * Nat.fib (n + 1) - (Nat.fib (m + 1) : ℤ) * Nat.fib n
      = (-1) ^ n * Nat.fib (m - n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have := dOcagne_sub_aux n k
  simpa using this

end Fibonacci
#print axioms Fibonacci.dOcagne
#print axioms Fibonacci.dOcagne_sub

