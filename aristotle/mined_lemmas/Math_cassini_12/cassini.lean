import Mathlib
import RequestProject.Cassini12

/-!
# Cassini 12, stated with Mathlib's `Nat.fib`

This companion file relates `Math.fib` to Mathlib's `Nat.fib`, proves the general Cassini
identity, and derives the `n = 12` instance in terms of `Nat.fib`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem cassini (n : ℕ) :
    (Nat.fib n : ℤ) * (Nat.fib (n + 2) : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
      have h2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
      push_cast [h, h2] at ih ⊢
      ring_nf
      ring_nf at ih
      linarith [ih]

/-- Cassini's identity at `n = 12`, stated with Mathlib's `Nat.fib`:
`F(11) * F(13) - F(12)^2 = (-1)^12`. -/
