/-!
# Cassini 11
Category: Pure Mathematics
Target: Math.cassini_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`,
`fib (n + 2) = fib n + fib (n + 1)`. -/

theorem fib_eq_nat_fib (n : ℕ) : fib n = Nat.fib n := by
  induction n using fib.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 n ih1 ih2 => rw [fib_add_two, Nat.fib_add_two, ih1, ih2, Nat.add_comm]

/-- Cassini's identity at `n = 11`, stated with Mathlib's `Nat.fib`. -/
