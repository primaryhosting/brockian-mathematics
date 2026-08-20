/-
# Cassini 15
Category: Pure Mathematics
Target: Math.cassini_15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- Cassini's identity for Fibonacci numbers, over the integers:
`F n * F (n+2) - F (n+1)^2 = (-1)^(n+1)`. -/

theorem fib_cassini (n : ℕ) :
    (Nat.fib n : ℤ) * Nat.fib (n + 2) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
    have h2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    rw [show n + 1 + 2 = n + 3 from rfl, h1]
    push_cast [h2]
    push_cast [h2] at ih
    ring_nf
    ring_nf at ih
    linarith [ih, pow_succ (-1 : ℤ) (n + 1)]

/-- Cassini's identity at `n = 15`: `F 14 * F 16 - F 15 ^ 2 = (-1)^15`. -/
