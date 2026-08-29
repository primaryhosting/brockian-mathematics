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

lemma pellSeq_y_gt (n : ℕ) : (n : ℤ) < (pellSeq n).2 := by
  induction n with
  | zero => norm_num [pellSeq]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := pellSeq_pos n
    simp only [pellSeq]
    push_cast
    nlinarith

/-- The Pell equation `x² - 10·y² = 1` has solutions with arbitrarily large `y`;
in particular it has infinitely many integer solutions. -/
