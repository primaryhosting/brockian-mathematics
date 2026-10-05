import Mathlib

/-!
# Pell 13, strengthened

A Mathlib-based companion to `Math.pell_13`: the solution set of `x² - 13·y² = 1`
in `ℤ × ℤ` is infinite, obtained by iterating the fundamental solution `(649, 180)`.
-/

namespace Math

/-- One step of multiplication by the fundamental unit `649 + 180·√13`. -/

lemma pellSol_nonneg (n : ℕ) : 0 ≤ (pellSol n).1 ∧ 0 ≤ (pellSol n).2 := by
  induction n with
  | zero => norm_num [pellSol]
  | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      simp only [pellSol, pellStep]
      constructor <;> positivity

