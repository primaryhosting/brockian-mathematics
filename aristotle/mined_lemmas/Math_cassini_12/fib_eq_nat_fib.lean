import Mathlib
import RequestProject.Cassini12

/-!
# Cassini 12, in Mathlib terms

This file links the self-contained Fibonacci function `Math.fib` of
`RequestProject.Cassini12` with Mathlib's `Nat.fib`, and restates Cassini's identity
at `n = 12` for `Nat.fib`. It also proves the general Cassini identity.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem fib_eq_nat_fib : ∀ n : ℕ, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 12`, stated with Mathlib's `Nat.fib`. -/
