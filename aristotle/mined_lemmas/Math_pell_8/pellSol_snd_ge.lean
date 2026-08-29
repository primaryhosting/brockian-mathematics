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

theorem pellSol_snd_ge (n : ℕ) : (n : ℤ) + 1 ≤ (pellSol n).2 := by
  induction n with
  | zero => norm_num [pellSol]
  | succ n ih =>
    have hx : 0 < (pellSol n).1 := (pellSol_pos n).1
    have hy : 0 < (pellSol n).2 := (pellSol_pos n).2
    simp only [pellSol, pellStep]
    push_cast
    linarith

/-- **Infinitely many solutions.** For every bound `N` the Pell equation
`x² - 8·y² = 1` has an integer solution with `y > N`; in particular it has
infinitely many nontrivial integer solutions. -/
