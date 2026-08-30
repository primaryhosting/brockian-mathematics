import Mathlib

/-!
# Catalan
Category: Fibonacci
Target: Fibonacci.catalan
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Fibonacci

/-- Cassini's identity: `F (m+1) ^ 2 - F m * F (m+2) = (-1)^m` over `ℤ`. -/

theorem cassini (m : ℕ) :
    (Nat.fib (m + 1) : ℤ) ^ 2 - (Nat.fib m : ℤ) * (Nat.fib (m + 2) : ℤ) = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
      have h2 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        exact_mod_cast Nat.fib_add_two (n := k)
      have h3 : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
        exact_mod_cast Nat.fib_add_two (n := k + 1)
      have hg : k + 1 + 2 = k + 3 := rfl
      have hg' : k + 1 + 1 = k + 2 := rfl
      rw [hg, hg', h3, pow_succ]
      linear_combination (Nat.fib (k + 2) : ℤ) * h2 - ih

/-- d'Ocagne's identity: `F (m+r) * F (m+1) - F m * F (m+r+1) = (-1)^m * F r`. -/
