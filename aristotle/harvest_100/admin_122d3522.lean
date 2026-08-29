/-
# Pell 13
Category: Pure Mathematics
Target: Math.pell_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pell 13
Category: Pure Mathematics
Target: Math.pell_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 13`.**  The equation `x² - 13 y² = 1` has a
nontrivial integer solution (one with `y ≠ 0`), namely `(x, y) = (649, 180)`:
`649² - 13 · 180² = 421201 - 421200 = 1`. -/
theorem pell_13 : ∃ x y : ℤ, x ^ 2 - 13 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨649, 180, by norm_num, by norm_num⟩

end Math

