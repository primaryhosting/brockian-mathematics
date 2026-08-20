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

lemma C3adj_det_sub_smul (μ : ℝ) :
    (C3adj - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = -(μ - 2) * (μ + 1) ^ 2 := by
  simp [C3adj, Matrix.det_fin_three, Fin.ext_iff]
  ring

