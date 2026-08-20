import Mathlib

/-!
# Molecular point groups are finite subgroups of O(3)

A molecule is modelled by the set `S ⊆ ℝ³` of its nuclear positions, placed so that the
centre of mass sits at the origin.  Its *point group* is the group of all orthogonal
transformations of `ℝ³` mapping the molecule onto itself; by construction this is a
subgroup of `O(3)` (here realised as the group `Matrix.orthogonalGroup (Fin 3) ℝ` of real
orthogonal `3 × 3` matrices acting on `Fin 3 → ℝ` by `mulVec`).

The main theorem `Chem.point_group_finite_O3` shows that this subgroup is finite for every
molecule with finitely many atoms whose positions span `ℝ³`.  The spanning hypothesis
cannot be dropped: a linear molecule such as CO₂ has the infinite point group `D∞h`
(all rotations about the molecular axis are symmetries).
-/

namespace Chem

open Matrix

/-- The orthogonal group `O(3)`, realised as real orthogonal `3 × 3` matrices. -/
abbrev O3 : Submonoid (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.orthogonalGroup (Fin 3) ℝ

/-- The natural action of `O(3)` on `ℝ³`. -/

lemma mem_pointGroup {S : Set (Fin 3 → ℝ)} {A : O3} :
    A ∈ pointGroup S ↔ act A '' S = S := Iff.rfl

/-- **Every molecular point group is a finite subgroup of `O(3)`.**

For a molecule with a finite set `S` of nuclear positions spanning `ℝ³`, the point
group `Chem.pointGroup S` — a subgroup of `O(3)` by construction — is finite. -/
