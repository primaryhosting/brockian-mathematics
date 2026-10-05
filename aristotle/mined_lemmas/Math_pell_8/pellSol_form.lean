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

theorem pellSol_form (n : ℕ) : (pellSol n).1 ^ 2 - 8 * (pellSol n).2 ^ 2 = 1 := by
  induction n with
  | zero => norm_num [pellSol]
  | succ n ih => rw [pellSol, pellStep_form, ih]

/-- Both coordinates of `pellSol n` are positive. -/
