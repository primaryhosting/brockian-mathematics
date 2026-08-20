/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- The adjacency matrix of the cycle graph `C₃`: every pair of distinct vertices
is joined by an edge, and there are no loops. -/

lemma two_cos_four_pi_div_three : 2 * Real.cos (2 * Real.pi * (2 : ℝ) / 3) = -1 := by
  rw [show 2 * Real.pi * (2 : ℝ) / 3 = Real.pi + Real.pi / 3 by ring, Real.cos_add,
    Real.cos_pi_div_three]
  simp

/-- The three Hückel values `2 cos (2πk/3)`, `k = 0, 1, 2`, are exactly `2, -1, -1`. -/
