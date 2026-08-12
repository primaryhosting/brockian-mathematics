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

/-- d'Ocagne's identity, stated in addition form to avoid natural subtraction:
`fib (m + n + 1) = fib (m+1) * fib (n+1) + fib m * fib n`. -/
theorem dOcagne (m n : ℕ) :
    (Nat.fib (m + n + 1) : ℤ)
      = (Nat.fib (m + 1) : ℤ) * (Nat.fib (n + 1) : ℤ) + (Nat.fib m : ℤ) * (Nat.fib n : ℤ) := by
  have h := Nat.fib_add m n
  have : (Nat.fib (m + n + 1) : ℤ)
      = (Nat.fib m : ℤ) * (Nat.fib n : ℤ) + (Nat.fib (m + 1) : ℤ) * (Nat.fib (n + 1) : ℤ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) h
  linarith

/-- Cassini-type identity: `fib (n+1)^2 - fib (n+1) * fib n - fib n ^ 2 = (-1)^n`. -/
theorem fib_sq_sub (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - (Nat.fib (n + 1) : ℤ) * (Nat.fib n : ℤ)
      - (Nat.fib n : ℤ) ^ 2 = (-1) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hf : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
      have := Nat.fib_add_two (n := k)
      exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) this
    rw [pow_succ]
    rw [show k + 1 + 1 = k + 2 from rfl, hf]
    ring_nf
    ring_nf at ih
    linarith

/-- d'Ocagne's identity in its classical subtractive form:
for `n ≤ m`, `fib m * fib (n+1) - fib (m+1) * fib n = (-1)^n * fib (m - n)`. -/
theorem dOcagne_sub (m n : ℕ) (h : n ≤ m) :
    (Nat.fib m : ℤ) * (Nat.fib (n + 1) : ℤ) - (Nat.fib (m + 1) : ℤ) * (Nat.fib n : ℤ)
      = (-1) ^ n * (Nat.fib (m - n) : ℤ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have hsub : n + k - n = k := by omega
  rw [hsub]
  match k with
  | 0 => simp [mul_comm]
  | (j + 1) =>
    have h1 : (Nat.fib (n + (j + 1)) : ℤ)
        = (Nat.fib (n + 1) : ℤ) * (Nat.fib (j + 1) : ℤ) + (Nat.fib n : ℤ) * (Nat.fib j : ℤ) := by
      have := dOcagne n j
      rw [show n + j + 1 = n + (j + 1) from by omega] at this
      exact this
    have h2 : (Nat.fib (n + (j + 1) + 1) : ℤ)
        = (Nat.fib (n + 1) : ℤ) * (Nat.fib (j + 2) : ℤ)
          + (Nat.fib n : ℤ) * (Nat.fib (j + 1) : ℤ) := by
      have := dOcagne n (j + 1)
      simpa [show j + 1 + 1 = j + 2 from rfl, show n + (j + 1) = n + j + 1 from by omega]
        using this
    have hf : (Nat.fib (j + 2) : ℤ) = (Nat.fib j : ℤ) + (Nat.fib (j + 1) : ℤ) := by
      have := Nat.fib_add_two (n := j)
      exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) this
    have hc := fib_sq_sub n
    rw [h1, h2, hf]
    linear_combination (Nat.fib (j + 1) : ℤ) * hc

end Fibonacci


