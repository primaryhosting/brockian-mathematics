import Mathlib
import RequestProject.Cassini7

/-!
# Cassini 7, stated with Mathlib's `Nat.fib`

This file connects the self-contained Fibonacci definition `Math.fib` of
`RequestProject/Cassini7.lean` with Mathlib's `Nat.fib`, and restates Cassini's
identity at `n = 7` in terms of `Nat.fib`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem fib_eq_natFib : ∀ n : ℕ, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_natFib n, fib_eq_natFib (n + 1)]

/-- Cassini's identity at `n = 7`, with Mathlib's `Nat.fib`:
`F(6) * F(8) - F(7)^2 = (-1)^7`. -/
