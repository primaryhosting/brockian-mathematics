import Mathlib
import RequestProject.Cassini6

/-!
# Cassini 6, Mathlib form

`Math.fib` agrees with Mathlib's `Nat.fib`, so Cassini's identity at `n = 6` also holds
in the form `Nat.fib 5 * Nat.fib 7 - Nat.fib 6 ^ 2 = (-1) ^ 6`.
-/

namespace Math


theorem fib_eq_natFib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_natFib n, fib_eq_natFib (n + 1)]

/-- Cassini's identity at `n = 6`, stated with Mathlib's `Nat.fib`. -/
