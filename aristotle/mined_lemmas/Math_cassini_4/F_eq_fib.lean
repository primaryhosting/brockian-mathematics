import Mathlib
import RequestProject.Cassini4

/-!
# Cassini 4, phrased with Mathlib's `Nat.fib`
-/

namespace Math

/-- The locally defined Fibonacci sequence agrees with Mathlib's `Nat.fib`. -/

theorem F_eq_fib : ∀ n, F n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [F, F_eq_fib n, F_eq_fib (n + 1), Nat.fib_add_two]

/-- Cassini's identity at `n = 4`, with Mathlib's `Nat.fib`:
`fib 3 * fib 5 - fib 4 ^ 2 = (-1) ^ 4`. -/
