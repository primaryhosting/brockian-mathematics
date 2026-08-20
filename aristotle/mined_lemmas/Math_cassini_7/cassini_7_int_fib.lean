import Mathlib
import RequestProject.Cassini7

/-!
# Cassini 7, stated with Mathlib's Fibonacci numbers

Companion to `RequestProject/Cassini7.lean`.  Here the same identity
`F 6 * F 8 - F 7 ^ 2 = (-1) ^ 7` is stated for Mathlib's `Nat.fib` (and `Int.fib`), and the
`Int.fib` version is deduced from the general Mathlib lemma
`Int.fib_succ_mul_fib_pred_sub_fib_sq` (**Cassini's identity**).
-/

namespace Math

/-- The locally defined `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem cassini_7_int_fib : Int.fib 8 * Int.fib 6 - Int.fib 7 ^ 2 = (-1) ^ 7 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 7
  norm_num at h
  simpa using h

/-- **Cassini's identity at `n = 7`** for `Nat.fib`: `F 6 * F 8 - F 7 ^ 2 = (-1) ^ 7`. -/
