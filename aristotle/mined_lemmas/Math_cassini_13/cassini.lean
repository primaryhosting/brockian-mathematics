import Mathlib
import RequestProject.Cassini13

/-!
# Cassini 13, stated for Mathlib's `Nat.fib`

Companion to `RequestProject/Cassini13.lean`.  We check that the locally defined
`Math.fib` agrees with Mathlib's `Nat.fib`, restate Cassini's identity at `n = 13`
for `Nat.fib`, and prove the general Cassini identity
`F (n+2) * F n - F (n+1) ^ 2 = (-1) ^ (n+1)` by induction.
-/

namespace Math


theorem cassini (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * (Nat.fib n : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_add_two (n := k + 1))
      have h3 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_add_two (n := k))
      rw [h3] at ih
      rw [show k + 1 + 2 = k + 3 from rfl, show k + 1 + 1 = k + 2 from rfl, h, h3, pow_succ]
      linear_combination -ih

/-- Cassini's identity at `n = 13`, for Mathlib's `Nat.fib`. -/
