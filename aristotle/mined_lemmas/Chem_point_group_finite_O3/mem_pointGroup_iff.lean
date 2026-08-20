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

/-!
## Setting

A *molecule* is modelled as a finite set of atomic positions in `ℝ³` which is not contained in
any plane through the origin (equivalently, the positions span `ℝ³`).  This non-degeneracy
hypothesis is genuinely needed: a linear molecule such as `CO₂` has the infinite point group
`D∞h`, so "molecular point groups are finite" is a statement about genuinely three-dimensional
molecules.

Its *point group* is the subgroup of `O(3)` consisting of those orthogonal transformations that
map the molecule onto itself.  (Only the positions are recorded; the point group of a molecule
with labelled atomic species is a subgroup of the group considered here, hence also finite.)

The key intermediate lemma is `Chem.eq_of_mulVec_eq_of_span`: an orthogonal transformation is
determined by its values on a spanning set.  Since a symmetry permutes the finitely many atoms,
this embeds the point group into the finite set of self-maps of the atom set.
-/

namespace Chem

open scoped Matrix

/-- `O3` is the orthogonal group `O(3)`: the group of real `3 × 3` matrices whose transpose is
their inverse. -/
abbrev O3 : Submonoid (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.orthogonalGroup (Fin 3) ℝ

@[simp]

theorem mem_pointGroup_iff {M : Molecule} {A : O3} :
    A ∈ pointGroup M ↔ M.atoms.image (act A) = M.atoms := Iff.rfl

/-- A symmetry of a molecule maps atoms to atoms. -/
