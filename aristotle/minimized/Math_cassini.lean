/-
# Cassini 7
Category: Pure Mathematics
Target: Math.cassini_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- Cassini's identity: `F(n) * F(n+2) - F(n+1)^2 = (-1)^(n+1)`, over the integers. -/

theorem cassini (n : ℕ) :
    (Nat.fib n : ℤ) * (Nat.fib (n + 2) : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h1 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
      have h2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
      push_cast [show k + 1 + 2 = k + 3 from rfl, h1, h2] at *
      ring_nf
      ring_nf at ih
      linarith [ih]

/-- Cassini's identity at `n = 7`: `F(6) * F(8) - F(7)^2 = (-1)^7`,
stated over the integers (`F(6) = 8`, `F(7) = 13`, `F(8) = 21`). -/
