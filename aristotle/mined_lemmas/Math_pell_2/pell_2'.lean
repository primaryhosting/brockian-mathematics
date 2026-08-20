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

theorem pell_2' : ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (by norm_num) not_isSquare_two_int

/-- For every natural number `n` there is a solution of `x² - 2·y² = 1` with `x > 0`
and `y > n`. Solutions are generated from `(3, 2)` by `(x, y) ↦ (3x + 4y, 2x + 3y)`,
i.e. by multiplication by the fundamental unit `3 + 2√2`. -/
