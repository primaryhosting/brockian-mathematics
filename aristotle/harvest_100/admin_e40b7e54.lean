/-
# Catalan
Category: Fibonacci
Target: Fibonacci.catalan
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

namespace Fibonacci

/-- Cassini's identity: `F (n+1) ^ 2 - F n * F (n+2) = (-1) ^ n`. -/
theorem cassini (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 2) = (-1) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 := Nat.fib_add_two (n := k)
    have h2 := Nat.fib_add_two (n := k + 1)
    push_cast [h1, h2] at *
    ring_nf at *
    linarith [ih]

/-- Value of `F (2 s + 1)` in terms of `F s` and `F (s+1)`. -/
private theorem fib_two_mul_succ (s : ℕ) :
    (Nat.fib (2 * s + 1) : ℤ) = Nat.fib (s + 1) ^ 2 + Nat.fib s ^ 2 := by
  rw [Nat.fib_two_mul_add_one]; push_cast; ring

/-- Value of `F (2 s + 2)` in terms of `F s` and `F (s+1)`. -/
private theorem fib_two_mul_add_two (s : ℕ) :
    (Nat.fib (2 * s + 2) : ℤ)
      = 2 * Nat.fib s * Nat.fib (s + 1) + Nat.fib (s + 1) ^ 2 := by
  have h : s + (s + 1) + 1 = 2 * s + 2 := by ring
  have hadd := Nat.fib_add s (s + 1)
  rw [h] at hadd
  have h2 := Nat.fib_add_two (n := s)
  rw [hadd]
  push_cast [h2]
  ring

/-- Catalan's identity, addition form (no natural subtraction):
for all `m r : ℕ`, `F (m + r) ^ 2 - F m * F (m + 2 * r) = (-1) ^ m * F r ^ 2`. -/
theorem catalan_add (m r : ℕ) :
    (Nat.fib (m + r) : ℤ) ^ 2 - Nat.fib m * Nat.fib (m + 2 * r)
      = (-1) ^ m * (Nat.fib r : ℤ) ^ 2 := by
  cases r with
  | zero => simp; ring
  | succ s =>
    have e1 : m + (s + 1) = m + s + 1 := by ring
    have e2 : m + 2 * (s + 1) = m + (2 * s + 1) + 1 := by ring
    have hmr : (Nat.fib (m + (s + 1)) : ℤ)
        = Nat.fib m * Nat.fib s + Nat.fib (m + 1) * Nat.fib (s + 1) := by
      rw [e1, Nat.fib_add]; push_cast; ring
    have hm2r : (Nat.fib (m + 2 * (s + 1)) : ℤ)
        = Nat.fib m * Nat.fib (2 * s + 1)
          + Nat.fib (m + 1) * Nat.fib (2 * s + 1 + 1) := by
      rw [e2, Nat.fib_add]; push_cast; ring
    have h21 : (2 * s + 1 + 1) = 2 * s + 2 := by ring
    rw [h21] at hm2r
    have hcas := cassini m
    have hfm2 : (Nat.fib (m + 2) : ℤ) = Nat.fib m + Nat.fib (m + 1) := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [hfm2] at hcas
    rw [hmr, hm2r, fib_two_mul_succ, fib_two_mul_add_two]
    nlinarith [hcas, sq_nonneg ((Nat.fib (s + 1) : ℤ))]

/-- Catalan's identity: for `r ≤ n`,
`F n ^ 2 - F (n - r) * F (n + r) = (-1) ^ (n - r) * F r ^ 2`. -/
theorem catalan (n r : ℕ) (h : r ≤ n) :
    (Nat.fib n : ℤ) ^ 2 - Nat.fib (n - r) * Nat.fib (n + r)
      = (-1) ^ (n - r) * (Nat.fib r : ℤ) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have hsub : r + m - r = m := by omega
  have hn : r + m = m + r := by ring
  rw [hsub, hn]
  have hnr : m + r + r = m + 2 * r := by ring
  rw [hnr]
  exact catalan_add m r

end Fibonacci

