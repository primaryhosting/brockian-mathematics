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

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 6`: `F 5 · F 7 − F 6 ^ 2 = (−1) ^ 6`,
i.e. `5 · 13 − 8 ^ 2 = 1`.  The computation is carried out in `ℤ`, so that the
subtraction and the sign `(−1) ^ 6` make sense. -/
