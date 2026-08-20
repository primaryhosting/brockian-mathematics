/-!
# Cassini 11
Category: Pure Mathematics
Target: Math.cassini_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

This agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_nat_fib` in
`RequestProject/Cassini11Mathlib.lean`). It is defined here so that this file,
which must begin with the header comment above, needs no `import` line. -/

theorem fib_eq_nat_fib : ∀ n : ℕ, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 11`, stated with Mathlib's `Nat.fib` and derived from
Mathlib's general Cassini identity `Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/
