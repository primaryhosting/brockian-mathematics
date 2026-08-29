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

theorem cassini_10_nat_fib :
    (Nat.fib 9 : ℤ) * (Nat.fib 11 : ℤ) - (Nat.fib 10 : ℤ) ^ 2 = (-1) ^ 10 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 10
  rw [show (10 : ℤ) + 1 = ((11 : ℕ) : ℤ) by norm_num,
    show (10 : ℤ) - 1 = ((9 : ℕ) : ℤ) by norm_num,
    show (10 : ℤ) = ((10 : ℕ) : ℤ) by norm_num, Int.fib_natCast, Int.fib_natCast,
    Int.fib_natCast] at h
  simpa [mul_comm] using h

/-- The two formulations agree. -/
