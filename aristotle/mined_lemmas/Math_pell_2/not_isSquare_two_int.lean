/-
# Pell 2
Category: Pure Mathematics
Target: Math.pell_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- **Pell's equation for `d = 2`.** The equation `x² - 2·y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0` (ruling out the trivial solutions `(±1, 0)`).
Witness: `(x, y) = (3, 2)`, since `9 - 8 = 1`. -/

theorem not_isSquare_two_int : ¬ IsSquare (2 : ℤ) := by
  rintro ⟨r, hr⟩
  rcases le_or_gt r 1 with h | h
  · rcases le_or_gt (-1) r with h2 | h2
    · interval_cases r <;> omega
    · nlinarith
  · nlinarith

/-- The same statement obtained from Mathlib's general existence theorem for Pell
equations, `Pell.exists_of_not_isSquare` (`Mathlib/NumberTheory/Pell.lean`), which says
that for `0 < d` with `d` not a square there are integers `x, y` with `x² - d·y² = 1`
and `y ≠ 0`. -/
