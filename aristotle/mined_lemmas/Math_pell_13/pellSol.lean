import Mathlib

/-!
# Pell 13, strengthened

A Mathlib-based companion to `Math.pell_13`: the solution set of `x² - 13·y² = 1`
in `ℤ × ℤ` is infinite, obtained by iterating the fundamental solution `(649, 180)`.
-/

namespace Math

/-- One step of multiplication by the fundamental unit `649 + 180·√13`. -/

def pellSol : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => pellStep (pellSol n)

