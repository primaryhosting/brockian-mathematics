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

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity at `n = 7`**: `F 6 * F 8 - F 7 ^ 2 = (-1) ^ 7`,
i.e. `8 * 21 - 13 ^ 2 = -1`, computed in `ℤ`. -/
