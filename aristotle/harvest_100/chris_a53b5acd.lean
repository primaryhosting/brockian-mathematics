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

/-- **d'Ocagne's identity**, stated in the subtraction-free additive form:
`fib (m + n + 1) = fib (m+1) * fib (n+1) + fib m * fib n`. -/
theorem dOcagne (m n : ℕ) :
    (Nat.fib (m + n + 1) : ℤ) = Nat.fib (m + 1) * Nat.fib (n + 1) + Nat.fib m * Nat.fib n := by
  rw [Nat.fib_add m n]
  push_cast
  ring

/-- Shifted form of d'Ocagne's identity, with `m` written as `n + k`. -/
theorem dOcagne_shift (n k : ℕ) :
    (Nat.fib (n + k) : ℤ) * Nat.fib (n + 1) - (Nat.fib (n + k + 1) : ℤ) * Nat.fib n
      = (-1) ^ n * Nat.fib k := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : Nat.fib (n + 1 + k) = Nat.fib (n + k + 1) := by ring_nf
      have h2 : Nat.fib (n + 1 + 1) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      have h3 : Nat.fib (n + 1 + k + 1) = Nat.fib (n + k) + Nat.fib (n + k + 1) := by
        have : n + 1 + k + 1 = (n + k) + 2 := by omega
        rw [this, Nat.fib_add_two]
        congr 1
        omega
      rw [h1, h2, h3]
      push_cast
      push_cast at ih
      ring_nf
      ring_nf at ih
      linarith [ih]

/-- **d'Ocagne's identity** in its classical subtractive form: for `n ≤ m`,
`fib m * fib (n+1) - fib (m+1) * fib n = (-1)^n * fib (m - n)`. -/
theorem dOcagne_sub (m n : ℕ) (h : n ≤ m) :
    (Nat.fib m : ℤ) * Nat.fib (n + 1) - (Nat.fib (m + 1) : ℤ) * Nat.fib n
      = (-1) ^ n * Nat.fib (m - n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have : n + k - n = k := by omega
  rw [this]
  exact dOcagne_shift n k

end Fibonacci

