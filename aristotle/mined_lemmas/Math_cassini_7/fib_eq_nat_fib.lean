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

theorem fib_eq_nat_fib (n : ℕ) : fib n = Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) =>
      rw [fib, Nat.fib_add_two, ih n (by omega), ih (n + 1) (by omega)]

/-- **Cassini's identity at `n = 7`** for `Int.fib`, obtained from the general Mathlib lemma
`Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/
