import Mathlib

/-!
# Pell 13, strengthened

A Mathlib-based companion to `Math.pell_13`: the solution set of `x² - 13·y² = 1`
in `ℤ × ℤ` is infinite, obtained by iterating the fundamental solution `(649, 180)`.
-/

namespace Math

/-- One step of multiplication by the fundamental unit `649 + 180·√13`. -/

def pellStep (p : ℤ × ℤ) : ℤ × ℤ := (649 * p.1 + 2340 * p.2, 180 * p.1 + 649 * p.2)

/-- The `n`-th power of the fundamental solution `(649, 180)`, starting from `(1, 0)`. -/
