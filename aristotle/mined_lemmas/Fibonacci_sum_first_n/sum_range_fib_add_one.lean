import Mathlib

/-!
# Sum First N
Category: Fibonacci
Target: Fibonacci.sum_first_n
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Fibonacci

/-- Auxiliary form avoiding truncated subtraction:
the sum of the first `n` Fibonacci numbers plus one equals `fib (n+1)`. -/

theorem sum_range_fib_add_one (n : ℕ) :
    (Finset.range n).sum (fun i => Nat.fib i) + 1 = Nat.fib (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.fib_add_two]
    omega

/-- The sum of the first `n` Fibonacci numbers is `fib (n+1) - 1`. -/
