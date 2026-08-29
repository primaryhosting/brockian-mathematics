import Mathlib

/-!
# Pell 13, strengthened

A Mathlib-based companion to `Math.pell_13`: the solution set of `x² - 13·y² = 1`
in `ℤ × ℤ` is infinite, obtained by iterating the fundamental solution `(649, 180)`.
-/

namespace Math

/-- One step of multiplication by the fundamental unit `649 + 180·√13`. -/

lemma pellSol_fst_pos (n : ℕ) : 1 ≤ (pellSol n).1 := by
  have h0 := (pellSol_nonneg n).1
  have h2 := (pellSol_nonneg n).2
  have h := pellSol_isSol n
  nlinarith [sq_nonneg (pellSol n).2]

