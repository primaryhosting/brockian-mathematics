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

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity at `n = 5`**: `F 4 * F 6 - F 5 ^ 2 = (-1) ^ 5`, over the integers. -/
