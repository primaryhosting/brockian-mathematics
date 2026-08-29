/-!
# Pell 11
Category: Pure Mathematics
Target: Math.pell_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 11·y² = 1` has a nontrivial integer solution,
namely `(x, y) = (10, 3)`: `10² - 11 * 3² = 100 - 99 = 1`. -/

theorem pell_11_via_mathlib : ∃ x y : ℤ, x ^ 2 - 11 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (by norm_num) (by decide +kernel)

end Math

