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

theorem fib_eq_nat_fib : ∀ n : ℕ, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1), Nat.fib_add_two]

/-- Cassini's identity at `n = 6`, stated with Mathlib's `Nat.fib`. -/
