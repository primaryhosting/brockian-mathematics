import Mathlib

/-!
# Catalan
Category: Fibonacci
Target: Fibonacci.catalan
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Fibonacci

open Nat

/-- Cassini's identity: `F(m+1)^2 - F(m) * F(m+2) = (-1)^m`. -/
theorem cassini (m : ℕ) :
    (Nat.fib (m + 1) : ℤ) ^ 2 - (Nat.fib m : ℤ) * (Nat.fib (m + 2) : ℤ) = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
      have h1 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (Nat.fib_add_two (n := k))
      have h2 : (Nat.fib (k + 1 + 2) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (Nat.fib_add_two (n := k + 1))
      rw [h1] at ih
      rw [h2, h1, pow_succ]
      linear_combination -ih

/-- Catalan's identity in addition form (avoiding natural subtraction):
`F(m+r)^2 - F(m) * F(m+2r) = (-1)^m * F(r)^2`. -/
theorem catalan_add (m r : ℕ) :
    (Nat.fib (m + r) : ℤ) ^ 2 - (Nat.fib m : ℤ) * (Nat.fib (m + 2 * r) : ℤ)
      = (-1) ^ m * (Nat.fib r : ℤ) ^ 2 := by
  cases r with
  | zero => simp [sq]
  | succ s =>
      have hsum : Nat.fib (m + (s + 1)) = Nat.fib m * Nat.fib s + Nat.fib (m + 1) * Nat.fib (s + 1) := by
        have := Nat.fib_add m s
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      have hbig : Nat.fib (m + 2 * (s + 1))
          = Nat.fib m * Nat.fib (2 * s + 1) + Nat.fib (m + 1) * Nat.fib (2 * s + 2) := by
        have := Nat.fib_add m (2 * s + 1)
        have h : m + 2 * (s + 1) = m + (2 * s + 1) + 1 := by ring
        rw [h]
        simpa [Nat.add_assoc] using this
      have hodd : Nat.fib (2 * s + 1) = Nat.fib (s + 1) ^ 2 + Nat.fib s ^ 2 :=
        Nat.fib_two_mul_add_one s
      have heven : Nat.fib (2 * s + 2) = Nat.fib (s + 1) * (2 * Nat.fib s + Nat.fib (s + 1)) :=
        Nat.fib_two_mul_add_two s
      have hc := cassini m
      have hfa : (Nat.fib (m + 2) : ℤ) = (Nat.fib m : ℤ) + (Nat.fib (m + 1) : ℤ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (Nat.fib_add_two (n := m))
      rw [hfa] at hc
      have hsum' : (Nat.fib (m + (s + 1)) : ℤ)
          = (Nat.fib m : ℤ) * (Nat.fib s : ℤ) + (Nat.fib (m + 1) : ℤ) * (Nat.fib (s + 1) : ℤ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hsum
      have hbig' : (Nat.fib (m + 2 * (s + 1)) : ℤ)
          = (Nat.fib m : ℤ) * ((Nat.fib (s + 1) : ℤ) ^ 2 + (Nat.fib s : ℤ) ^ 2)
            + (Nat.fib (m + 1) : ℤ)
              * ((Nat.fib (s + 1) : ℤ) * (2 * (Nat.fib s : ℤ) + (Nat.fib (s + 1) : ℤ))) := by
        rw [hbig]
        push_cast [hodd, heven]
        ring
      rw [hsum', hbig']
      linear_combination (Nat.fib (s + 1) : ℤ) ^ 2 * hc

/-- Catalan's identity in the original subtraction form: for `r ≤ n`,
`F(n)^2 - F(n-r) * F(n+r) = (-1)^(n-r) * F(r)^2`. -/
theorem catalan {n r : ℕ} (h : r ≤ n) :
    (Nat.fib n : ℤ) ^ 2 - (Nat.fib (n - r) : ℤ) * (Nat.fib (n + r) : ℤ)
      = (-1) ^ (n - r) * (Nat.fib r : ℤ) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : r + m - r = m := by omega
  have h2 : r + m + r = m + 2 * r := by ring
  have h3 : r + m = m + r := by ring
  rw [h1, h2, h3]
  exact catalan_add m r

end Fibonacci

