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

theorem real_roots_quinticPhi_ge (hab : b < a) :
    2 ≤ Fintype.card ((quinticPhi ℚ a b).rootSet ℝ) := by
  have q_ne_zero : quinticPhi ℚ a b ≠ 0 := (monic_quinticPhi a b).ne_zero
  obtain ⟨x, y, hxy, hx, hy⟩ := real_roots_quinticPhi_ge_aux a b hab
  have key : ↑({x, y} : Finset ℝ) ⊆ (quinticPhi ℚ a b).rootSet ℝ := by
    simp [Set.insert_subset, mem_rootSet_of_ne q_ne_zero, hx, hy]
  convert Fintype.card_le_of_embedding (Set.embeddingOfSubset _ _ key)
  simp only [Finset.coe_sort_coe, Fintype.card_coe, Finset.card_singleton,
    Finset.card_insert_of_notMem (mt Finset.mem_singleton.mp hxy)]

