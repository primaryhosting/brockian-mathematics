/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Complex Finset

namespace Chem

/-- The circulant form of the adjacency matrix of the cycle graph `C₁₁`,
with vertices indexed by `ZMod 11`. -/

theorem adjMatrix_cycleGraph_eq : (SimpleGraph.cycleGraph 11).adjMatrix ℂ = cycAdj := by
  ext i j
  have h : (i - j = -1) ↔ (j - i = 1) := by
    rw [← neg_inj, neg_sub]; simp
  simp [SimpleGraph.adjMatrix_apply, cycAdj, Matrix.circulant, SimpleGraph.cycleGraph_adj, h]

/-- The standard additive character of `ZMod 11`, `k ↦ exp (2πik/11)`. -/
noncomputable abbrev ee : AddChar (ZMod 11) ℂ := ZMod.stdAddChar

/-- The discrete Fourier matrix `P i k = exp (2πi·ik/11)`. -/
