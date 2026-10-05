import Mathlib
import RequestProject.Cassini12

/-!
# Cassini 12, stated with Mathlib's `Nat.fib`

This companion file relates `Math.fib` to Mathlib's `Nat.fib`, proves the general Cassini
identity, and derives the `n = 12` instance in terms of `Nat.fib`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem fib_eq_natFib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_natFib n, fib_eq_natFib (n + 1), Nat.add_comm]

/-- Cassini's identity: `F(n) * F(n+2) - F(n+1)^2 = (-1)^(n+1)`. -/
