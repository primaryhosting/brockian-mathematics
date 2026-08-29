/-!
# Pell 8
Category: Pure Mathematics
Target: Math.pell_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Math

/-- The Pell equation `x² - 8·y² = 1` has a nontrivial integer solution
(one with `y ≠ 0`), namely `(x, y) = (3, 1)`, since `3² - 8·1² = 9 - 8 = 1`. -/

theorem pell_8_via_mathlib :
    ∃ x y : ℕ, x * x - 8 * y * y = 1 ∧ y ≠ 0 :=
  ⟨Pell.xn (a := 3) (by decide) 1, Pell.yn (a := 3) (by decide) 1,
    Pell.pell_eq (by decide) 1, by decide⟩

/-- The Brahmagupta/Pell composition step for `d = 8`: from a solution `(x, y)` we get
the new solution `(3x + 8y, x + 3y)`. -/
