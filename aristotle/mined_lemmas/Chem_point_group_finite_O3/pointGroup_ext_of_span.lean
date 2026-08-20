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

theorem pointGroup_ext_of_span {S : Finset (Fin 3 → ℝ)}
    (hspan : Submodule.span ℝ (S : Set (Fin 3 → ℝ)) = ⊤)
    {A B : Matrix.orthogonalGroup (Fin 3) ℝ}
    (h : ∀ x ∈ S, (A : Matrix (Fin 3) (Fin 3) ℝ).mulVec x
      = (B : Matrix (Fin 3) (Fin 3) ℝ).mulVec x) : A = B := by
  have hlin : Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) ℝ)
      = Matrix.mulVecLin (B : Matrix (Fin 3) (Fin 3) ℝ) :=
    LinearMap.ext_on hspan (fun x hx => h x hx)
  have : (A : Matrix (Fin 3) (Fin 3) ℝ) = (B : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    have := congrFun (congrArg (fun f => f (Pi.single j (1 : ℝ))) hlin) i
    simpa [Matrix.mulVec_single] using this
  exact Subtype.ext this

/-- The action of a point-group element on the atoms of the molecule: a symmetry
operation permutes the atomic positions. -/
