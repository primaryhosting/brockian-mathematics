import Mathlib
import RequestProject.Cassini14

/-!
# Cassini 14 (Mathlib restatement)

This file identifies the self-contained Fibonacci sequence `Math.F` of
`RequestProject/Cassini14.lean` with Mathlib's `Nat.fib`, and restates Cassini's
identity at `n = 14` in terms of `Nat.fib`.
-/

namespace Math


theorem F_eq_fib (n : ℕ) : F n = Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) =>
      rw [F, Nat.fib_add_two, ih n (by omega), ih (n + 1) (by omega)]

/-- Cassini's identity at `n = 14`, phrased with Mathlib's `Nat.fib`. -/
