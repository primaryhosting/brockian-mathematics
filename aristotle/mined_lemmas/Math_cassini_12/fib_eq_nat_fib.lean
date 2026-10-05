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

theorem fib_eq_nat_fib : ∀ n : ℕ, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 12`, stated with Mathlib's `Nat.fib`, obtained by
specializing Mathlib's `Int.fib_succ_mul_fib_pred_sub_fib_sq` to `n = 12`. -/
