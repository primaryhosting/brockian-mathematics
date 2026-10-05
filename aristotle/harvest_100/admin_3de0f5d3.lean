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

set_option grind.warning false

namespace Fibonacci

/-- Cassini's identity in the form `F_{n+1}^2 - F_{n+1} F_n - F_n^2 = (-1)^n`. -/
theorem cassini (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - (Nat.fib (n + 1) : ℤ) * (Nat.fib n : ℤ)
      - (Nat.fib n : ℤ) ^ 2 = (-1) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have h : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      have h' : ((Nat.fib (n + 2) : ℤ)) = (Nat.fib n : ℤ) + (Nat.fib (n + 1) : ℤ) := by
        exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) h
      rw [h', pow_succ]
      linear_combination -ih

/-- Vajda's identity (shifted so that no natural subtraction occurs):
`F_{n+i+1} F_{n+j+1} - F_n F_{n+i+j+2} = (-1)^n F_{i+1} F_{j+1}`. -/
theorem vajda (n i j : ℕ) :
    (Nat.fib (n + i + 1) : ℤ) * (Nat.fib (n + j + 1) : ℤ)
      - (Nat.fib n : ℤ) * (Nat.fib (n + i + j + 2) : ℤ)
      = (-1) ^ n * ((Nat.fib (i + 1) : ℤ) * (Nat.fib (j + 1) : ℤ)) := by
  have e1 : (Nat.fib (n + i + 1) : ℤ)
      = (Nat.fib n : ℤ) * (Nat.fib i : ℤ) + (Nat.fib (n + 1) : ℤ) * (Nat.fib (i + 1) : ℤ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) (Nat.fib_add n i)
  have e2 : (Nat.fib (n + j + 1) : ℤ)
      = (Nat.fib n : ℤ) * (Nat.fib j : ℤ) + (Nat.fib (n + 1) : ℤ) * (Nat.fib (j + 1) : ℤ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) (Nat.fib_add n j)
  have e3 : (Nat.fib (n + i + j + 2) : ℤ)
      = (Nat.fib n : ℤ) * (Nat.fib (i + j + 1) : ℤ)
        + (Nat.fib (n + 1) : ℤ) * (Nat.fib (i + j + 2) : ℤ) := by
    have := congrArg (fun k : ℕ => (k : ℤ)) (Nat.fib_add n (i + j + 1))
    simp only at this
    rw [show n + i + j + 2 = n + (i + j + 1) + 1 by ring]
    exact_mod_cast this
  have e4 : (Nat.fib (i + j + 1) : ℤ)
      = (Nat.fib i : ℤ) * (Nat.fib j : ℤ) + (Nat.fib (i + 1) : ℤ) * (Nat.fib (j + 1) : ℤ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) (Nat.fib_add i j)
  have e5 : (Nat.fib (i + j + 2) : ℤ)
      = (Nat.fib i : ℤ) * (Nat.fib (j + 1) : ℤ)
        + (Nat.fib (i + 1) : ℤ) * (Nat.fib (j + 2) : ℤ) := by
    have := congrArg (fun k : ℕ => (k : ℤ)) (Nat.fib_add i (j + 1))
    simp only at this
    rw [show i + j + 2 = i + (j + 1) + 1 by ring]
    exact_mod_cast this
  have e6 : (Nat.fib (j + 2) : ℤ) = (Nat.fib j : ℤ) + (Nat.fib (j + 1) : ℤ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) (Nat.fib_add_two (n := j))
  have hc := cassini n
  rw [e1, e2, e3, e4, e5, e6]
  linear_combination ((Nat.fib (i + 1) : ℤ) * (Nat.fib (j + 1) : ℤ)) * hc

/-- Catalan's identity in addition form (no natural subtraction):
`F_{m+r}^2 - F_m F_{m+2r} = (-1)^m F_r^2`. -/
theorem catalan_add (m r : ℕ) :
    (Nat.fib (m + r) : ℤ) ^ 2 - (Nat.fib m : ℤ) * (Nat.fib (m + 2 * r) : ℤ)
      = (-1) ^ m * (Nat.fib r : ℤ) ^ 2 := by
  cases r with
  | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, Nat.fib_zero]
      ring
  | succ k =>
      have h := vajda m k k
      have h1 : m + k + 1 = m + (k + 1) := by ring
      have h2 : m + k + k + 2 = m + 2 * (k + 1) := by ring
      rw [h1, h2] at h
      rw [sq, sq]
      linarith [h]

/-- Catalan's identity: for `r ≤ n`,
`F_n^2 - F_{n-r} F_{n+r} = (-1)^{n-r} F_r^2`. -/
theorem catalan (n r : ℕ) (h : r ≤ n) :
    (Nat.fib n : ℤ) ^ 2 - (Nat.fib (n - r) : ℤ) * (Nat.fib (n + r) : ℤ)
      = (-1) ^ (n - r) * (Nat.fib r : ℤ) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have hm : r + m - r = m := by omega
  rw [hm]
  have := catalan_add m r
  rw [show r + m + r = m + 2 * r by ring, show r + m = m + r by ring]
  linarith [this]

end Fibonacci

