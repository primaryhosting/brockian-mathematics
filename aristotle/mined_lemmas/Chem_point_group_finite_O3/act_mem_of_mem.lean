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
## Molecular point groups are finite subgroups of `O(3)`

A molecule is modelled by the set `S ⊆ ℝ³` of its atomic positions, taken in a
coordinate system whose origin is the centroid of the molecule, so that every
symmetry operation of the molecule is a linear orthogonal transformation of `ℝ³`
mapping `S` onto itself.

`Chem.pointGroup S` is, by construction, a subgroup of the orthogonal group
`O(3)` (the group of `3 × 3` real orthogonal matrices).  The main theorem
`Chem.point_group_finite_O3` states that for a genuine molecule — finitely many
atoms, not all lying in a common line or plane through the origin, i.e. the
positions span `ℝ³` — this subgroup is *finite*.
-/

namespace Chem

open Matrix

/-- Euclidean three-space, described by coordinate vectors. -/
abbrev Vec3 : Type := Fin 3 → ℝ

/-- `O(3)`, the orthogonal group of `3 × 3` real matrices. -/
abbrev O3 : Type := Matrix.orthogonalGroup (Fin 3) ℝ

/-- The natural action of an orthogonal matrix on a vector of `ℝ³`. -/

lemma act_mem_of_mem {S : Set Vec3} {A : O3} (hA : A ∈ pointGroup S) {v : Vec3}
    (hv : v ∈ S) : act A v ∈ S := by
  have : act A v ∈ act A '' S := ⟨v, hv, rfl⟩
  rwa [hA] at this

/-- **Every molecular point group is a finite subgroup of `O(3)`.**

For a molecule with finitely many atoms, positioned at the points of `S` (centred
so that the symmetry operations are linear), whose positions span `ℝ³`, the point
group `Chem.pointGroup S` — a subgroup of the orthogonal group `O(3)` by
construction — is finite. -/
