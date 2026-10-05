/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Complex Polynomial Matrix SimpleGraph

namespace Chem

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

lemma adjMatrix_mul_F18 :
    (SimpleGraph.cycleGraph 18).adjMatrix ℂ * F18
      = F18 * Matrix.diagonal (fun k : Fin 18 => ((huckelEnergy k : ℝ) : ℂ)) := by
  ext j k
  have h1 : ((SimpleGraph.cycleGraph 18).adjMatrix ℂ * F18) j k
      = (((SimpleGraph.cycleGraph 18).adjMatrix ℂ) *ᵥ (fun m => F18 m k)) j := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h1, SimpleGraph.adjMatrix_mulVec_apply,
    SimpleGraph.cycleGraph_neighborFinset (n := 16), Finset.sum_pair (fin18_sub_ne_add j),
    fin18_sub_one, Matrix.mul_diagonal, F18_apply, F18_apply, F18_apply,
    fin18_add_pow (zeta18_pow_pow_18 _), fin18_add_pow (zeta18_pow_pow_18 _),
    ← zeta18_pow_add_inv k]
  norm_num
  ring

/-- The adjacency matrix of `C₁₈` is conjugate to the diagonal matrix of Hückel energies. -/
