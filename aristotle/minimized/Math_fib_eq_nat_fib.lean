import Mathlib
import RequestProject.Math

/-!
# Cassini 10, via Mathlib's Fibonacci numbers

This file links `Math.fib` (defined in `RequestProject.Math`, which cannot carry an `import`
line) with Mathlib's `Nat.fib`, and derives the `n = 10` case of Cassini's identity from
Mathlib's general statement `Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem fib_eq_nat_fib : ∀ n : ℕ, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- **Cassini's identity at `n = 10`** for Mathlib's `Nat.fib`:
`F 9 * F 11 - (F 10)^2 = (-1)^10`.

Proved as an instance of Mathlib's `Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity at `n = 10`**: `F 9 * F 11 - (F 10)^2 = (-1)^10`, computed in `ℤ`. -/
