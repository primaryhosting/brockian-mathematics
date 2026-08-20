/-!
# Cassini 5
Category: Pure Mathematics
Target: Math.cassini_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, with `fib 0 = 0` and `fib 1 = 1`. -/

theorem fib_eq_nat_fib (n : ℕ) : fib n = Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) =>
      rw [fib, Nat.fib_add_two, ih n (by omega), ih (n + 1) (by omega)]

/-- Cassini's identity at `n = 5`, stated with Mathlib's `Nat.fib`. -/
