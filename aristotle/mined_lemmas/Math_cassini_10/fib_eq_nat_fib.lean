import Mathlib
import RequestProject.Main

/-!
# Cassini's identity at `n = 10`, in Mathlib terms

This file links the self-contained `Math.fib` of `RequestProject/Main.lean` with Mathlib's
`Nat.fib`, and restates `Math.cassini_10` using `Nat.fib`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem fib_eq_nat_fib : ∀ n : ℕ, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 10`, stated with Mathlib's `Nat.fib`. -/
