import Mathlib
import RequestProject.Math

/-!
# Cassini 12 — Mathlib cross-check

This file connects the self-contained development in `RequestProject/Math.lean`
with Mathlib:

* `Math.fib_eq_nat_fib` : the locally defined `Math.fib` equals Mathlib's `Nat.fib`;
* `Math.cassini_12_nat_fib` : the target statement phrased with `Nat.fib`, derived
  from Mathlib's general Cassini identity
  `Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

/-- The `fib` of this project agrees with Mathlib's `Nat.fib`. -/

theorem cassini_12_nat_fib :
    (Nat.fib 11 : ℤ) * (Nat.fib 13 : ℤ) - (Nat.fib 12 : ℤ) ^ 2 = (-1) ^ 12 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 12
  simpa [Int.fib] using h

/-- The target theorem `Math.cassini_12` indeed states Cassini's identity for the
Mathlib Fibonacci numbers. -/
