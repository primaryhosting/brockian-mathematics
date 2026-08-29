/-!
# Cassini 7
Category: Pure Mathematics
Target: Math.cassini_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.
(This file must begin with the required header comment, which Lean treats as a module
docstring and therefore forbids any `import` afterwards; hence the sequence is defined
here from scratch. The file `RequestProject/CassiniMathlib.lean` proves that this
sequence agrees with Mathlib's `Nat.fib` and restates the result for `Nat.fib`.) -/

theorem fib_eq_nat_fib : ∀ n : ℕ, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 7` for Mathlib's `Nat.fib`:
`F 6 * F 8 - F 7 ^ 2 = (-1) ^ 7`. -/
