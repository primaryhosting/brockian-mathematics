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

lemma adjMatrix_conj :
    (SimpleGraph.cycleGraph 18).adjMatrix ℂ
      = (F18_isUnit.unit : Matrix (Fin 18) (Fin 18) ℂ)
        * Matrix.diagonal (fun k : Fin 18 => ((huckelEnergy k : ℝ) : ℂ))
        * ((F18_isUnit.unit)⁻¹ : (Matrix (Fin 18) (Fin 18) ℂ)ˣ) := by
  have hv : (F18_isUnit.unit : Matrix (Fin 18) (Fin 18) ℂ) = F18 := F18_isUnit.unit_spec
  have hmul : (F18_isUnit.unit : Matrix (Fin 18) (Fin 18) ℂ)
      * ((F18_isUnit.unit)⁻¹ : (Matrix (Fin 18) (Fin 18) ℂ)ˣ) = 1 := Units.mul_inv _
  calc (SimpleGraph.cycleGraph 18).adjMatrix ℂ
      = (SimpleGraph.cycleGraph 18).adjMatrix ℂ
          * ((F18_isUnit.unit : Matrix (Fin 18) (Fin 18) ℂ)
            * ((F18_isUnit.unit)⁻¹ : (Matrix (Fin 18) (Fin 18) ℂ)ˣ)) := by rw [hmul, mul_one]
    _ = ((SimpleGraph.cycleGraph 18).adjMatrix ℂ * F18)
          * ((F18_isUnit.unit)⁻¹ : (Matrix (Fin 18) (Fin 18) ℂ)ˣ) := by rw [hv, mul_assoc]
    _ = _ := by rw [adjMatrix_mul_F18, hv]

/--
**Hückel theory for the annulene `C₁₈`.**

The characteristic polynomial of the adjacency matrix of the cycle graph `C₁₈` factors as
`∏_{k=0}^{17} (X - 2 cos (2πk/18))`, and consequently the spectrum of the adjacency matrix
is exactly the set of Hückel energies `{2 cos (2πk/18) : k = 0, …, 17}`.
-/
