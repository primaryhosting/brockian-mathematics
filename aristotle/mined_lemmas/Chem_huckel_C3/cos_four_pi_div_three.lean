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

open Real Matrix

/-- The adjacency matrix of the cycle graph `C₃` (the complete graph on 3 vertices):
zero on the diagonal, one off the diagonal. -/

lemma cos_four_pi_div_three : Real.cos (4 * Real.pi / 3) = -(1 / 2) := by
  have h : (4 : ℝ) * Real.pi / 3 = 2 * Real.pi - 2 * Real.pi / 3 := by ring
  rw [h, Real.cos_two_pi_sub, cos_two_pi_div_three]

/-- The three Hückel eigenvalues `2 cos(2πk/3)` are `2, -1, -1`. -/
