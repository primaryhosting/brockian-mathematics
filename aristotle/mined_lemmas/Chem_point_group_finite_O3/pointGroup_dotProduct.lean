/-
# Point Group Finite O 3
Category: Chemistry
Target: Chem.point_group_finite_O3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Point Group Finite O 3
Category: Chemistry
Target: Chem.point_group_finite_O3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Chem

open Matrix

/-- The point group of a molecule, modelled as a finite set `S` of atomic positions in
`ℝ³`: it is the subgroup of the orthogonal group `O(3)` consisting of those orthogonal
transformations that map the molecule onto itself. -/

theorem pointGroup_dotProduct (S : Finset (Fin 3 → ℝ)) (A : pointGroup S)
    (x y : Fin 3 → ℝ) :
    (((A : Matrix.orthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ).mulVec x) ⬝ᵥ
        (((A : Matrix.orthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ).mulVec y)
      = x ⬝ᵥ y := by
  have h : ((A : Matrix.orthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ *
      ((A : Matrix.orthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    have := (A : Matrix.orthogonalGroup (Fin 3) ℝ).2.1
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose] using this
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, h, Matrix.vecMul_one]

/-- Non-vacuity: the three unit vectors along the coordinate axes span `ℝ³`. -/
