import Mathlib
import RequestProject.Cassini2

/-!
# Cassini 2, in terms of Mathlib's `Nat.fib`
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem fib_eq_nat_fib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 2`, stated with Mathlib's `Nat.fib`. -/
