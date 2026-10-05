/-
# Catalan
Category: Fibonacci
Target: Fibonacci.catalan
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Catalan
Category: Fibonacci
Target: Fibonacci.catalan
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

/-- Cassini's identity, in the form `F(m+1)² - F(m+1)F(m) - F(m)² = (-1)ᵐ` over `ℤ`. -/
theorem cassini_aux (m : ℕ) :
    (Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m - (Nat.fib m : ℤ) ^ 2 = (-1) ^ m := by
  induction m with
  | zero => norm_num
  | succ k ih =>
      have h : (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
        exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) (Nat.fib_add_two (n := k))
      rw [h, pow_succ]
      linear_combination (-1 : ℤ) * ih

/-- Addition formula for Fibonacci numbers over `ℤ`, valid for all `r` (including `r = 0`). -/
theorem fib_add_int (m r : ℕ) :
    (Nat.fib (m + r) : ℤ)
      = Nat.fib m * ((Nat.fib (r + 1) : ℤ) - Nat.fib r) + Nat.fib (m + 1) * Nat.fib r := by
  cases r with
  | zero => simp
  | succ s =>
      have h : Nat.fib (m + s + 1) = Nat.fib m * Nat.fib s + Nat.fib (m + 1) * Nat.fib (s + 1) :=
        Nat.fib_add m s
      have h2 : (Nat.fib (s + 2) : ℤ) = Nat.fib s + Nat.fib (s + 1) := by
        exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) (Nat.fib_add_two (n := s))
      have h1 : (Nat.fib (m + (s + 1)) : ℤ)
          = Nat.fib m * Nat.fib s + Nat.fib (m + 1) * Nat.fib (s + 1) := by
        have : m + (s + 1) = m + s + 1 := by omega
        rw [this]
        exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) h
      rw [h1, show s + 1 + 1 = s + 2 from rfl, h2]
      ring

/-- Doubling formula over `ℤ` (no truncated subtraction). -/
theorem fib_two_mul_int (r : ℕ) :
    (Nat.fib (2 * r) : ℤ) = Nat.fib r * (2 * (Nat.fib (r + 1) : ℤ) - Nat.fib r) := by
  have hle : Nat.fib r ≤ 2 * Nat.fib (r + 1) := by
    have := Nat.fib_le_fib_succ (n := r)
    omega
  have h := Nat.fib_two_mul r
  have : (Nat.fib (2 * r) : ℤ) = (Nat.fib r : ℤ) * ((2 * Nat.fib (r + 1) - Nat.fib r : ℕ) : ℤ) := by
    exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) h
  rw [this]
  push_cast [Nat.cast_sub hle]
  ring

theorem fib_two_mul_add_one_int (r : ℕ) :
    (Nat.fib (2 * r + 1) : ℤ) = (Nat.fib (r + 1) : ℤ) ^ 2 + (Nat.fib r : ℤ) ^ 2 := by
  exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) (Nat.fib_two_mul_add_one r)

/-- **Catalan's identity** (addition form, avoiding natural subtraction):
for all `m r : ℕ`, `F(m+r)² - F(m)·F(m+2r) = (-1)^m · F(r)²`. -/
theorem catalan_add (m r : ℕ) :
    (Nat.fib (m + r) : ℤ) ^ 2 - (Nat.fib m : ℤ) * Nat.fib (m + 2 * r)
      = (-1) ^ m * (Nat.fib r : ℤ) ^ 2 := by
  rw [fib_add_int m r, fib_add_int m (2 * r), fib_two_mul_int r, fib_two_mul_add_one_int r,
    ← cassini_aux m]
  ring

/-- **Catalan's identity** in the subtraction form: for `r ≤ n`,
`F(n)² - F(n-r)·F(n+r) = (-1)^(n-r) · F(r)²`. -/
theorem catalan {n r : ℕ} (h : r ≤ n) :
    (Nat.fib n : ℤ) ^ 2 - (Nat.fib (n - r) : ℤ) * Nat.fib (n + r)
      = (-1) ^ (n - r) * (Nat.fib r : ℤ) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + r := ⟨n - r, by omega⟩
  have h1 : m + r - r = m := by omega
  have h2 : m + r + r = m + 2 * r := by omega
  rw [h1, h2]
  exact catalan_add m r

end Fibonacci

