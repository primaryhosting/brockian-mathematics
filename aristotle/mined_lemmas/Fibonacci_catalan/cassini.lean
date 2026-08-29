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

namespace Fibonacci

/-- Cassini's identity: `F(m+1)^2 - F(m) * F(m+2) = (-1)^m`, over `ℤ`. -/

theorem cassini (m : ℕ) :
    (Nat.fib (m + 1) : ℤ) ^ 2 - (Nat.fib m : ℤ) * (Nat.fib (m + 2) : ℤ) = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
    have h1 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
      simpa using Nat.fib_add_two (n := k + 1)
    have h2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    have h1' : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h1
    have h2' : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h2
    rw [h2'] at ih
    rw [show k + 1 + 1 = k + 2 from rfl, show k + 1 + 2 = k + 3 from rfl, h1', h2', pow_succ]
    linear_combination -ih

/-- **Catalan's identity** for Fibonacci numbers, in addition form (no `Nat` subtraction):
for all `m r : ℕ`, `F(m+r)^2 - F(m) * F(m+2r) = (-1)^m * F(r)^2`. -/
