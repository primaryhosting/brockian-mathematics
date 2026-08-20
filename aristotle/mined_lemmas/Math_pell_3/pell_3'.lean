/-
# Pell 3
Category: Pure Mathematics
Target: Math.pell_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pell 3
Category: Pure Mathematics
Target: Math.pell_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 3`**: `x² − 3·y² = 1` has a nontrivial integer solution,
i.e. one with `y ≠ 0` (equivalently `x ≠ ±1`).  The fundamental solution is `(x, y) = (2, 1)`. -/

theorem pell_3' : ∃ x y : ℤ, x ^ 2 - 3 * y ^ 2 = 1 ∧ y ≠ 0 := by
  refine Pell.exists_of_not_isSquare (by norm_num) ?_
  rintro ⟨r, hr⟩
  have h1 : r ≤ 2 := by nlinarith
  have h2 : -2 ≤ r := by nlinarith
  interval_cases r <;> omega

/-- The sequence of solutions generated from `(2, 1)` by the fundamental automorphism
`(x, y) ↦ (2x + 3y, x + 2y)` of `x² − 3y² = 1` (multiplication by `2 + √3`). -/
