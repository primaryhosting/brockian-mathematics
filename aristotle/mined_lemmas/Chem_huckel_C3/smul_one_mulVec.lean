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

private lemma smul_one_mulVec (μ : ℝ) (v : Fin 3 → ℝ) :
    ((μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).mulVec v) = μ • v := by
  ext i
  simp [Matrix.mulVec, Matrix.one_apply, dotProduct]

/-- **Key intermediate lemma.** A real number `μ` is an eigenvalue of the adjacency
matrix of `C₃` if and only if `μ = 2` or `μ = -1`. -/
