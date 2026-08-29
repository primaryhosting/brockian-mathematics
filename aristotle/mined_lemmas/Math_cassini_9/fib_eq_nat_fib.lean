/-!
# Cassini 9
Category: Pure Mathematics
Target: Math.cassini_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
(Defined here rather than taken from Mathlib because the required file header is a module
docstring, which Lean requires to precede any `import` command; the file
`RequestProject/CassiniMathlib.lean` proves this agrees with `Nat.fib` and restates the
result in Mathlib terms.) -/

theorem fib_eq_nat_fib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 9` for Mathlib's `Nat.fib`:
`F(8) * F(10) - F(9)^2 = (-1)^9`. -/
