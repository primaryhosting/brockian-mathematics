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

theorem cassini_5_nat_fib :
    (Nat.fib 4 : ℤ) * (Nat.fib 6 : ℤ) - (Nat.fib 5 : ℤ) ^ 2 = (-1) ^ 5 := by
  simpa [fib_eq_nat_fib] using cassini_5

/-- Cassini's identity at `n = 5`, derived from Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq : ∀ n : ℤ,
  Int.fib (n + 1) * Int.fib (n - 1) - Int.fib n ^ 2 = (-1) ^ n.natAbs`. -/
