/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

/-- The adjacency matrix of the cycle graph `C₃` (every pair of distinct vertices
is adjacent). In Hückel theory this is the (shifted, scaled) Hamiltonian of the
cyclic three-carbon π-system. -/

lemma C3adj_det_sub (μ : ℝ) :
    (C3adj - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = -(μ - 2) * (μ + 1) ^ 2 := by
  simp [Matrix.det_fin_three, C3adj, Matrix.sub_apply, Matrix.smul_apply, Fin.ext_iff]
  ring

/-- **Hückel theory for the cyclic three-carbon π-system.**
A real number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₃`
if and only if it is of the form `2 * cos (2πk/3)` for some `k ∈ {0, 1, 2}`. -/
