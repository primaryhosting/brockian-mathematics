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

lemma cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
  have h : (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]

