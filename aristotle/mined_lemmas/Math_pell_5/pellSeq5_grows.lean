/-!
# Pell 5
Category: Pure Mathematics
Target: Math.pell_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 5`.** The equation `x² - 5·y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0` (so that `x ≠ ±1`): take `(x, y) = (9, 4)`,
since `9² - 5·4² = 81 - 80 = 1`. -/

theorem pellSeq5_grows (n : ℕ) :
    1 ≤ (pellSeq5 n).1 ∧ (n : ℤ) + 4 ≤ (pellSeq5 n).2 := by
  induction n with
  | zero => exact ⟨by decide, by decide⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩ <;> simp only [pellSeq5] <;> push_cast <;> omega

/-- **Pell's equation for `d = 5` has infinitely many solutions.** For every bound `N`
there is a solution of `x² - 5·y² = 1` with `y > N`. -/
