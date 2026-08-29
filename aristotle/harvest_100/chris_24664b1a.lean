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
def act (A : O3) (v : Vec3) : Vec3 := (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v

@[simp] lemma act_one (v : Vec3) : act 1 v = v := by
  simp [act]

lemma act_mul (A B : O3) (v : Vec3) : act (A * B) v = act A (act B v) := by
  simp [act, Submonoid.coe_mul, mulVec_mulVec]

lemma act_inv_act (A : O3) (v : Vec3) : act A⁻¹ (act A v) = v := by
  rw [← act_mul, inv_mul_cancel, act_one]

lemma act_act_inv (A : O3) (v : Vec3) : act A (act A⁻¹ v) = v := by
  rw [← act_mul, mul_inv_cancel, act_one]

/-- The **point group** of a molecule whose atomic positions are `S`: the group of
all orthogonal transformations of `ℝ³` carrying the set of atoms onto itself.
It is a subgroup of `O(3)` by construction. -/
def pointGroup (S : Set Vec3) : Subgroup O3 where
  carrier := {A : O3 | act A '' S = S}
  one_mem' := by
    simp
  mul_mem' := by
    intro A B hA hB
    simp only [Set.mem_setOf_eq] at hA hB ⊢
    have : act (A * B) '' S = act A '' (act B '' S) := by
      rw [Set.image_image]
      exact Set.image_congr' (fun v => act_mul A B v)
    rw [this, hB, hA]
  inv_mem' := by
    intro A hA
    simp only [Set.mem_setOf_eq] at hA ⊢
    calc act A⁻¹ '' S = act A⁻¹ '' (act A '' S) := by rw [hA]
      _ = S := by
          rw [Set.image_image]
          simp only [act_inv_act]
          exact Set.image_id S

lemma act_mem_of_mem {S : Set Vec3} {A : O3} (hA : A ∈ pointGroup S) {v : Vec3}
    (hv : v ∈ S) : act A v ∈ S := by
  have : act A v ∈ act A '' S := ⟨v, hv, rfl⟩
  rwa [hA] at this

/-- **Every molecular point group is a finite subgroup of `O(3)`.**

For a molecule with finitely many atoms, positioned at the points of `S` (centred
so that the symmetry operations are linear), whose positions span `ℝ³`, the point
group `Chem.pointGroup S` — a subgroup of the orthogonal group `O(3)` by
construction — is finite. -/
theorem point_group_finite_O3 (S : Set Vec3) (hfin : S.Finite)
    (hspan : Submodule.span ℝ S = ⊤) : Finite (pointGroup S) := by
  haveI : Finite S := hfin.to_subtype
  -- A symmetry is determined by the permutation it induces on the (finitely many) atoms.
  refine Finite.of_injective
    (f := fun A : pointGroup S => fun v : S => (⟨act A.1 v.1, act_mem_of_mem A.2 v.2⟩ : S)) ?_
  intro A B hAB
  have hEq : Set.EqOn (⇑(mulVecLin (A.1 : Matrix (Fin 3) (Fin 3) ℝ)))
      (⇑(mulVecLin (B.1 : Matrix (Fin 3) (Fin 3) ℝ))) S := by
    intro v hv
    have := congrFun hAB ⟨v, hv⟩
    simpa [act, Matrix.mulVecLin_apply] using congrArg Subtype.val this
  have hlin : mulVecLin (A.1 : Matrix (Fin 3) (Fin 3) ℝ)
      = mulVecLin (B.1 : Matrix (Fin 3) (Fin 3) ℝ) := LinearMap.ext_on hspan hEq
  have hmat : (A.1 : Matrix (Fin 3) (Fin 3) ℝ) = (B.1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    simpa [Matrix.mulVecLin_apply] using congrArg (fun f => f v) (congrArg DFunLike.coe hlin)
  exact Subtype.ext (Subtype.ext hmat)

/-!
### Non-vacuity

The hypotheses of `Chem.point_group_finite_O3` are satisfiable: the three atoms of
a molecule placed at the standard basis vectors form a finite spanning set, so its
point group is a finite subgroup of `O(3)`.
-/

/-- The standard basis vectors span `ℝ³`. -/
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

