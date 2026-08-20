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

def atomMap (S : Finset (Fin 3 → ℝ)) (A : pointGroup S) : {y // y ∈ S} → {y // y ∈ S} :=
  fun x => ⟨((A : Matrix.orthogonalGroup (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ).mulVec (x : Fin 3 → ℝ), (A.2 (x : Fin 3 → ℝ)).1 x.2⟩

/-- If the atoms span `ℝ³`, a symmetry operation is determined by the permutation it
induces on the atoms. -/
