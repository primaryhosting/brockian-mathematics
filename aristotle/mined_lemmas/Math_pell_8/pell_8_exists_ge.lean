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

theorem pell_8_exists_ge (n : ℕ) :
    ∃ x y : ℤ, x ^ 2 - 8 * y ^ 2 = 1 ∧ 1 ≤ x ∧ (n : ℤ) ≤ y := by
  induction n with
  | zero => exact ⟨1, 0, by norm_num, by norm_num, by norm_num⟩
  | succ n ih =>
    obtain ⟨x, y, hxy, hx, hy⟩ := ih
    have hy0 : (0 : ℤ) ≤ y := le_trans (by positivity) hy
    refine ⟨3 * x + 8 * y, x + 3 * y, pell_8_step hxy, by linarith, ?_⟩
    push_cast
    linarith

/-- The equation `x² - 8·y² = 1` has infinitely many integer solutions: for every bound `N`
there is a solution with `y > N`. -/
