/-
# Pell 8
Category: Pure Mathematics
Target: Math.pell_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pell 8
Category: Pure Mathematics
Target: Math.pell_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 8·y² = 1` has a nontrivial integer solution, i.e. one with
`y ≠ 0` (so `x ≠ ±1`).  Witness: `(x, y) = (3, 1)`, since `9 - 8 = 1`. -/

theorem not_isSquare_eight : ¬ IsSquare (8 : ℤ) := by
  rintro ⟨r, hr⟩
  have h1 : r ≤ 3 := by nlinarith
  have h2 : -3 ≤ r := by nlinarith
  interval_cases r <;> omega

/-- An alternative, non-constructive proof of `Math.pell_8`, obtained from Mathlib's general
existence theorem for Pell equations, `Pell.exists_of_not_isSquare`. -/
