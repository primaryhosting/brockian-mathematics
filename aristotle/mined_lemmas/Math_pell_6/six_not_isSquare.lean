/-
# Pell 6
Category: Pure Mathematics
Target: Math.pell_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pell 6
Category: Pure Mathematics
Target: Math.pell_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Pell's equation `x² - 6·y² = 1` has a nontrivial integer solution,
witnessed by `(x, y) = (5, 2)`, since `25 - 6 * 4 = 1`. -/

theorem six_not_isSquare : ¬ IsSquare (6 : ℤ) := by
  decide +kernel

/-- The same statement obtained from Mathlib's general existence theorem for Pell
equations, `Pell.exists_of_not_isSquare`: for `0 < d` with `d` not a square, the
equation `x² - d·y² = 1` has a solution with `y ≠ 0`. -/
