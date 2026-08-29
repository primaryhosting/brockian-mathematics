import Mathlib

/-!
# Pell 8 — infinitely many solutions

A Mathlib-based strengthening of `Math.pell_8`: the equation `x² - 8·y² = 1` has
solutions with arbitrarily large `y`, hence infinitely many integer solutions.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

/-- From one solution of `x² - 8y² = 1` with `x ≥ 1`, `y ≥ 0`, one produces a larger one. -/

theorem pell_8_large (n : ℕ) :
    ∃ x y : ℤ, x ^ 2 - 8 * y ^ 2 = 1 ∧ 1 ≤ x ∧ (n : ℤ) ≤ y := by
  induction n with
  | zero => exact ⟨3, 1, by decide, by decide, by decide⟩
  | succ n ih =>
      obtain ⟨x, y, h, hx, hy⟩ := ih
      have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
      refine ⟨3 * x + 8 * y, x + 3 * y, pell_8_step h, by linarith, ?_⟩
      push_cast
      linarith

/-- The set of integer solutions of `x² - 8y² = 1` is infinite. -/
