/-!
# Pell 11
Category: Pure Mathematics
Target: Math.pell_11
Statement: x² − 11·y² = 1 has a nontrivial integer solution (Pell).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Pell 11
Category: Pure Mathematics
Target: Math.pell_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Math

/-- The Pell equation `x² - 11·y² = 1` has a nontrivial integer solution,
i.e. one with `y ≠ 0` (equivalently `x ≠ ±1`). Witness: `(x, y) = (10, 3)`. -/
theorem pell_11 : ∃ x y : ℤ, x ^ 2 - 11 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨10, 3, by norm_num, by norm_num⟩

end Math

