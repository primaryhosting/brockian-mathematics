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

lemma two_cos_two_pi_div_three : 2 * Real.cos (2 * Real.pi * (1 : ℝ) / 3) = -1 := by
  rw [show 2 * Real.pi * (1 : ℝ) / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]
  norm_num

/-- `2 cos (4π/3) = -1`. -/
