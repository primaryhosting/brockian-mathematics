/-
Supplement to `RequestProject/Cassini14.lean`: identifies the Fibonacci sequence
`Math.fib` used there with Mathlib's `Nat.fib`, and restates Cassini 14 for `Nat.fib`.
-/
import Mathlib
import RequestProject.Cassini14

namespace Math


theorem fib_eq_natFib (n : Nat) : fib n = (Nat.fib n : Int) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (k + 2) =>
        rw [fib_add_two, Nat.fib_add_two, ih k (by omega), ih (k + 1) (by omega)]
        push_cast
        ring

/-- Cassini's identity at `n = 14`, stated with Mathlib's `Nat.fib`:
`F 13 * F 15 - F 14 ^ 2 = (-1) ^ 14`. -/
