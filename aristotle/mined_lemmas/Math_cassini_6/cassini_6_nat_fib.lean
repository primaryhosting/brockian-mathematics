import Mathlib
import RequestProject.Cassini6

/-!
# Cassini 6, Mathlib version

Companion file to `RequestProject/Cassini6.lean`.  We check that the Fibonacci
sequence `Math.fib` used there agrees with Mathlib's `Nat.fib`, restate
Cassini's identity at `n = 6` for `Nat.fib`, and derive it once more from
Mathlib's general Cassini identity `Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem cassini_6_nat_fib :
    (Nat.fib 5 : ℤ) * (Nat.fib 7 : ℤ) - (Nat.fib 6 : ℤ) ^ 2 = (-1) ^ 6 := by
  simpa [fib_eq_nat_fib] using Math.cassini_6

/-- Cassini's identity at `n = 6`, obtained from Mathlib's general Cassini
identity `Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/
