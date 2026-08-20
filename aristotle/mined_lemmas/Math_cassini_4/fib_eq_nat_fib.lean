/-!
# Cassini 4
Category: Pure Mathematics
Target: Math.cassini_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean requires all `import` commands to precede any other command, including
module doc comments.  Since the requested header must be the very first thing in
this file, the file is kept self-contained (no imports beyond the core prelude)
and the Fibonacci sequence is defined directly below with the standard recursion,
matching `Nat.fib` (`F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`).
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`. -/

theorem fib_eq_nat_fib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 4`, stated with Mathlib's `Nat.fib`. -/
