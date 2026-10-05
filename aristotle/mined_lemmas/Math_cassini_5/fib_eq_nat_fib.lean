import Mathlib
import RequestProject.Math

/-!
# Cassini 5 — Mathlib companion file

This file connects the self-contained development in `RequestProject/Math.lean` with
Mathlib: it shows `Math.fib = Nat.fib`, restates `Math.cassini_5` in terms of `Nat.fib`,
and re-derives it from Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

/-- The locally defined Fibonacci sequence agrees with Mathlib's `Nat.fib`. -/

theorem fib_eq_nat_fib : ∀ n : ℕ, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 5`, phrased with Mathlib's `Nat.fib`. -/
