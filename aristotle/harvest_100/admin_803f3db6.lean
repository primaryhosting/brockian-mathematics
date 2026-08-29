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

/-- **d'Ocagne's identity**, stated in the subtraction-free additive form:
`F_{m+n+1} = F_{m+1} F_{n+1} + F_m F_n` for all natural numbers `m, n`. -/
theorem dOcagne (m n : ℕ) :
    (Nat.fib (m + n + 1) : ℤ)
      = (Nat.fib (m + 1) : ℤ) * (Nat.fib (n + 1) : ℤ) + (Nat.fib m : ℤ) * (Nat.fib n : ℤ) := by
  have h := Nat.fib_add m n
  zify at h
  linarith

/-- Auxiliary shifted form of the signed d'Ocagne identity:
`F_{n+k} F_{n+1} - F_{n+k+1} F_n = (-1)^n F_k`. -/
theorem dOcagne_shift (n k : ℕ) :
    (Nat.fib (n + k) : ℤ) * (Nat.fib (n + 1) : ℤ)
        - (Nat.fib (n + k + 1) : ℤ) * (Nat.fib n : ℤ)
      = (-1 : ℤ) ^ n * (Nat.fib k : ℤ) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
      have h1 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      have h2 : Nat.fib (n + k + 2) = Nat.fib (n + k) + Nat.fib (n + k + 1) := Nat.fib_add_two
      have e1 : n + 1 + k = n + k + 1 := by omega
      have e2 : n + k + 1 + 1 = n + k + 2 := by omega
      have e3 : n + 1 + 1 = n + 2 := by omega
      rw [e1, e2, e3, h1, h2]
      have hk := ih k
      push_cast
      push_cast at hk
      ring_nf
      ring_nf at hk
      linarith

/-- **d'Ocagne's identity** in its classical signed form: for `n ≤ m`,
`F_m F_{n+1} - F_{m+1} F_n = (-1)^n F_{m-n}`. -/
theorem dOcagne_sub (m n : ℕ) (h : n ≤ m) :
    (Nat.fib m : ℤ) * (Nat.fib (n + 1) : ℤ) - (Nat.fib (m + 1) : ℤ) * (Nat.fib n : ℤ)
      = (-1 : ℤ) ^ n * (Nat.fib (m - n) : ℤ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have hk : n + k - n = k := by omega
  rw [hk]
  exact dOcagne_shift n k

end Fibonacci

#print axioms Fibonacci.dOcagne
#print axioms Fibonacci.dOcagne_sub

