import Mathlib
import RequestProject.Math

/-!
# Cassini 3, stated with Mathlib's `Nat.fib`

This file links the self-contained `Math.fib` used in `RequestProject.Math` with
Mathlib's `Nat.fib`, and restates Cassini's identity at `n = 3` for `Nat.fib`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem fib_eq_nat_fib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 3` for Mathlib's `Nat.fib`. -/
