import Mathlib

/-!
# Pell 8 — companion results

Supplementary development for the target theorem `Math.pell_8`
(`RequestProject/Pell8.lean`): the Pell equation `x² - 8·y² = 1` has not merely one
nontrivial integer solution, but infinitely many, generated from `(3, 1)` by the
automorphism `(x, y) ↦ (3x + 8y, x + 3y)` of the form `x² - 8y²`.
-/

namespace Math

/-- One application of the Pell automorphism attached to the fundamental
solution `(3, 1)` of `x² - 8y² = 1`. -/

theorem pell_8_solutions_infinite :
    {p : ℤ × ℤ | p.1 ^ 2 - 8 * p.2 ^ 2 = 1 ∧ p.2 ≠ 0}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨⟨bx, by'⟩, hb⟩
  obtain ⟨x, y, hxy, hy⟩ := pell_8_infinitely_many (max by' 0)
  have hy0 : y ≠ 0 := by have := le_max_right by' 0; omega
  have hby : by' < y := lt_of_le_of_lt (le_max_left by' 0) hy
  have := hb (show ((x, y) : ℤ × ℤ) ∈ _ from ⟨hxy, hy0⟩)
  exact absurd this.2 (by simpa using hby)

end Math

/-!
# Pell 8
Category: Pure Mathematics
Target: Math.pell_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 8·y² = 1` has a nontrivial integer solution
(i.e. one with `y ≠ 0`): take `(x, y) = (3, 1)`. -/
