import Mathlib

/-!
# Pell 11
Category: Pure Mathematics
Target: Math.pell_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 11·y² = 1` has a nontrivial integer solution
(i.e. one with `y ≠ 0`): the fundamental solution is `(x, y) = (10, 3)`,
since `10² - 11·3² = 100 - 99 = 1`. -/
theorem pell_11 : ∃ x y : ℤ, x ^ 2 - 11 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨10, 3, by norm_num, by norm_num⟩

end Math

