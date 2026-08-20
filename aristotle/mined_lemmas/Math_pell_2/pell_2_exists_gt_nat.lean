/-
# Pell 2
Category: Pure Mathematics
Target: Math.pell_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- **Pell's equation for `d = 2`.** The equation `x² - 2·y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0` (ruling out the trivial solutions `(±1, 0)`).
Witness: `(x, y) = (3, 2)`, since `9 - 8 = 1`. -/

theorem pell_2_exists_gt_nat (n : ℕ) :
    ∃ x y : ℤ, x ^ 2 - 2 * y ^ 2 = 1 ∧ 0 < x ∧ (n : ℤ) < y := by
  induction n with
  | zero => exact ⟨3, 2, by norm_num, by norm_num, by norm_num⟩
  | succ k ih =>
      obtain ⟨x, y, hxy, hx, hy⟩ := ih
      have hk : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
      refine ⟨3 * x + 4 * y, 2 * x + 3 * y, by ring_nf; linarith [hxy], by linarith, ?_⟩
      push_cast
      linarith

/-- The solutions of `x² - 2·y² = 1` have arbitrarily large `y`. -/
