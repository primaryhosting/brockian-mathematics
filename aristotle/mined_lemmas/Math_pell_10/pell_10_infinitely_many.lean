import Mathlib

/-!
# Pell 10 (Mathlib companion)

The main target `Math.pell_10` lives in `RequestProject/Pell10.lean`.  Here we record the
same statement phrased with Mathlib's `ℤ`, together with the stronger fact that the Pell
equation `x² - 10·y² = 1` has infinitely many integer solutions, obtained by iterating the
fundamental solution `(19, 6)`.
-/

namespace Math

/-- Iterating the fundamental solution `(19, 6)` of `x² - 10·y² = 1`:
`(x, y) ↦ (19x + 60y, 6x + 19y)` (multiplication by `19 + 6√10`). -/

theorem pell_10_infinitely_many (N : ℤ) :
    ∃ x y : ℤ, x ^ 2 - 10 * y ^ 2 = 1 ∧ N < y := by
  refine ⟨(pellSeq N.toNat).1, (pellSeq N.toNat).2, pellSeq_sol _, ?_⟩
  have h := pellSeq_y_gt N.toNat
  have : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  omega

/-- The solution set of `x² - 10·y² = 1` in `ℤ × ℤ` is infinite. -/
