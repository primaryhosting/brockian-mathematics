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

theorem atomMap_injective {S : Finset (Fin 3 → ℝ)}
    (hspan : Submodule.span ℝ (S : Set (Fin 3 → ℝ)) = ⊤) :
    Function.Injective (atomMap S) := by
  intro A B hAB
  apply Subtype.ext
  refine pointGroup_ext_of_span hspan (fun x hx => ?_)
  exact congrArg Subtype.val (congrFun hAB ⟨x, hx⟩)

/-- **Every molecular point group is a finite subgroup of `O(3)`.**

A molecule is given by a finite set `S` of atomic positions in `ℝ³` which spans `ℝ³`
(i.e. the molecule is not contained in a plane through the origin, so the geometry
determines the symmetry operations).  Its point group `pointGroup S` is by construction a
subgroup of the orthogonal group `O(3) = Matrix.orthogonalGroup (Fin 3) ℝ`, and this
subgroup is finite: a symmetry operation permutes the atoms, and since the atoms span
`ℝ³` it is determined by that permutation. -/
