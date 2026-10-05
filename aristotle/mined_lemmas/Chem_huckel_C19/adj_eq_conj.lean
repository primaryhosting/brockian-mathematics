import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Matrix

namespace Chem

/-- A primitive 19-th root of unity. -/

theorem adj_eq_conj : (SimpleGraph.cycleGraph 19).adjMatrix ℂ =
    (U19 : Matrix (Fin 19) (Fin 19) ℂ) * D19 * ((U19⁻¹ : (Matrix (Fin 19) (Fin 19) ℂ)ˣ) :
      Matrix (Fin 19) (Fin 19) ℂ) := by
  have h1 : ((U19 : (Matrix (Fin 19) (Fin 19) ℂ)ˣ) : Matrix (Fin 19) (Fin 19) ℂ) = F19 := rfl
  have h2 : ((U19⁻¹ : (Matrix (Fin 19) (Fin 19) ℂ)ˣ) : Matrix (Fin 19) (Fin 19) ℂ) = G19 := rfl
  rw [h1, h2, ← adj_mul_F, mul_assoc, F_mul_G, mul_one]

/-- **Hückel theory for the cycle `C₁₉`.**  The eigenvalues of the adjacency matrix of the
cycle graph on 19 vertices are exactly the numbers `2 * cos (2 * π * k / 19)`, `k = 0, …, 18`. -/
