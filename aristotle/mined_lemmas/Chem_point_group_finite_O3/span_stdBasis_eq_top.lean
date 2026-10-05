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

lemma span_stdBasis_eq_top :
    Submodule.span ℝ (Set.range (fun i : Fin 3 => (Pi.single i 1 : Vec3))) = ⊤ := by
  rw [show (Set.range (fun i : Fin 3 => (Pi.single i 1 : Vec3)))
      = Set.range (Pi.basisFun ℝ (Fin 3)) from
    congrArg Set.range (funext fun i => (Pi.basisFun_apply ℝ (Fin 3) i).symm)]
  exact (Pi.basisFun ℝ (Fin 3)).span_eq

example : Finite (pointGroup (Set.range (fun i : Fin 3 => (Pi.single i 1 : Vec3)))) :=
  point_group_finite_O3 _ (Set.finite_range _) span_stdBasis_eq_top


end Chem

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

