import Mathlib

/-!
# Pell 13, strengthened

A Mathlib-based companion to `Math.pell_13`: the solution set of `x² - 13·y² = 1`
in `ℤ × ℤ` is infinite, obtained by iterating the fundamental solution `(649, 180)`.
-/

namespace Math

/-- One step of multiplication by the fundamental unit `649 + 180·√13`. -/

lemma pellSol_isSol (n : ℕ) : (pellSol n).1 ^ 2 - 13 * (pellSol n).2 ^ 2 = 1 := by
  induction n with
  | zero => norm_num [pellSol]
  | succ n ih =>
      simp only [pellSol, pellStep]
      nlinarith [ih]

