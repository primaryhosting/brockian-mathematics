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

theorem pell_2_exists_gt (N : ℤ) : ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = 1 ∧ N < y := by
  obtain ⟨x, y, h1, _, h3⟩ := pell_2_exists_gt_nat N.toNat
  exact ⟨x, y, h1, lt_of_le_of_lt (Int.self_le_toNat N) h3⟩

/-- There are infinitely many integer solutions of `x² - 2·y² = 1`. -/
