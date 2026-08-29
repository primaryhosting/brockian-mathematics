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

def pellStep (p : ℤ × ℤ) : ℤ × ℤ := (3 * p.1 + 8 * p.2, p.1 + 3 * p.2)

/-- The sequence of solutions of `x² - 8y² = 1` obtained by iterating `pellStep`
from the fundamental solution `(3, 1)`. -/
