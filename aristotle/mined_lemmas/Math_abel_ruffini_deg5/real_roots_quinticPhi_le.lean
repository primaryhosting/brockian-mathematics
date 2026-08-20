/- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`, so the
requested header is reproduced verbatim as a block comment here, and again as the module
docstring immediately after the import.)

# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

/-!
The development below is adapted from the Mathlib archive file
`Archive/Wiedijk100Theorems/AbelRuffini.lean` (Thomas Browning, Apache 2.0), which is not
importable from this project, and follows the classical Galois-theoretic proof of the Abel–Ruffini

theorem real_roots_quinticPhi_le : Fintype.card ((quinticPhi ℚ a b).rootSet ℝ) ≤ 3 := by
  rw [← map_quinticPhi a b (algebraMap ℤ ℚ), quinticPhi, ← one_mul (X ^ 5), ← C_1]
  apply (card_rootSet_le_derivative _).trans
    (Nat.succ_le_succ ((card_rootSet_le_derivative _).trans (Nat.succ_le_succ _)))
  suffices (Polynomial.rootSet (C (20 : ℚ) * X ^ 3) ℝ).Subsingleton by
    norm_num [Fintype.card_le_one_iff_subsingleton, ← mul_assoc] at *
    exact this
  rw [rootSet_C_mul_X_pow] <;>
  norm_num

