/-
# Consecutive Coprime
Category: Fibonacci
Target: Fibonacci.consecutive_coprime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Consecutive Coprime
Category: Fibonacci
Target: Fibonacci.consecutive_coprime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Fibonacci

/-- Consecutive Fibonacci numbers are coprime: `gcd (fib n) (fib (n+1)) = 1`.

The proof is by induction on `n`, using `fib (n + 2) = fib n + fib (n + 1)`, so that
`gcd (fib (n+1)) (fib (n+2)) = gcd (fib (n+1)) (fib n) = gcd (fib n) (fib (n+1))`. -/
theorem consecutive_coprime (n : ℕ) : Nat.Coprime (Nat.fib n) (Nat.fib (n + 1)) := by
  induction n with
  | zero => simp [Nat.Coprime]
  | succ k ih =>
    have h : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    unfold Nat.Coprime at ih ⊢
    rw [h, Nat.add_comm (Nat.fib k) (Nat.fib (k + 1)), Nat.gcd_self_add_right, Nat.gcd_comm]
    exact ih

end Fibonacci

