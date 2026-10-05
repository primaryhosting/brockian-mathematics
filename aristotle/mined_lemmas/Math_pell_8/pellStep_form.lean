import Mathlib

/-!
# Pell 8 — companion results

Supplementary development for the target theorem `Math.pell_8`
(`RequestProject/Pell8.lean`): the Pell equation `x² - 8·y² = 1` has not merely one
nontrivial integer solution, but infinitely many, generated from `(3, 1)` by the
automorphism `(x, y) ↦ (3x + 8y, x + 3y)` of the form `x² - 8y²`.
-/

namespace Math

/-- One application of the Pell automorphism attached to the fundamental
solution `(3, 1)` of `x² - 8y² = 1`. -/

theorem pellStep_form (p : ℤ × ℤ) :
    (pellStep p).1 ^ 2 - 8 * (pellStep p).2 ^ 2 = p.1 ^ 2 - 8 * p.2 ^ 2 := by
  simp only [pellStep]
  ring

/-- Every term of `pellSol` solves `x² - 8y² = 1`. -/
