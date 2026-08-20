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
theorem O3.coe_one : ((1 : O3) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := rfl

@[simp]
theorem O3.coe_mul (A B : O3) :
    ((A * B : O3) : Matrix (Fin 3) (Fin 3) ℝ) = (A : Matrix (Fin 3) (Fin 3) ℝ) * B := rfl

/-- The action of an element of `O(3)` on a vector of `ℝ³`. -/
def act (A : O3) (v : Fin 3 → ℝ) : Fin 3 → ℝ := (A : Matrix (Fin 3) (Fin 3) ℝ).mulVec v

@[simp]
theorem act_one (v : Fin 3 → ℝ) : act 1 v = v := by
  simp [act]

@[simp]
theorem act_mul (A B : O3) (v : Fin 3 → ℝ) : act (A * B) v = act A (act B v) := by
  simp [act, Matrix.mulVec_mulVec]

@[simp]
theorem act_inv_act (A : O3) (v : Fin 3 → ℝ) : act A⁻¹ (act A v) = v := by
  rw [← act_mul, inv_mul_cancel, act_one]

/-- **Key intermediate lemma.**  Two orthogonal transformations that agree on a set spanning
`ℝ³` are equal. -/
theorem eq_of_mulVec_eq_of_span {S : Set (Fin 3 → ℝ)} (hS : Submodule.span ℝ S = ⊤)
    {A B : O3} (h : ∀ v ∈ S, act A v = act B v) : A = B := by
  have hlin : Matrix.toLin' (A : Matrix (Fin 3) (Fin 3) ℝ)
      = Matrix.toLin' (B : Matrix (Fin 3) (Fin 3) ℝ) := by
    refine LinearMap.ext_on hS ?_
    intro v hv
    simpa [Matrix.toLin'_apply, act] using h v hv
  have : (A : Matrix (Fin 3) (Fin 3) ℝ) = (B : Matrix (Fin 3) (Fin 3) ℝ) :=
    Matrix.toLin'.injective hlin
  exact Subtype.ext this

/-- A molecule: a finite set of atomic positions in `ℝ³` spanning `ℝ³`. -/
structure Molecule where
  /-- The positions of the atoms. -/
  atoms : Finset (Fin 3 → ℝ)
  /-- Non-degeneracy: the molecule is genuinely three-dimensional. -/
  spanning : Submodule.span ℝ (atoms : Set (Fin 3 → ℝ)) = ⊤

/-- The point group of a molecule: the subgroup of `O(3)` of orthogonal transformations mapping
the set of atoms onto itself. -/
def pointGroup (M : Molecule) : Subgroup O3 where
  carrier := {A | M.atoms.image (act A) = M.atoms}
  one_mem' := by
    show M.atoms.image (act 1) = M.atoms
    rw [show act (1 : O3) = id from funext act_one, Finset.image_id]
  mul_mem' := by
    intro A B hA hB
    simp only [Set.mem_setOf_eq] at *
    rw [show act (A * B) = act A ∘ act B from funext (act_mul A B),
      ← Finset.image_image, hB, hA]
  inv_mem' := by
    intro A hA
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hA]
    rw [Finset.image_image, show act A⁻¹ ∘ act A = id from funext (act_inv_act A),
      Finset.image_id]

theorem mem_pointGroup_iff {M : Molecule} {A : O3} :
    A ∈ pointGroup M ↔ M.atoms.image (act A) = M.atoms := Iff.rfl

/-- A symmetry of a molecule maps atoms to atoms. -/
theorem act_mem_atoms {M : Molecule} {A : O3} (hA : A ∈ pointGroup M) {v : Fin 3 → ℝ}
    (hv : v ∈ M.atoms) : act A v ∈ M.atoms := by
  rw [← mem_pointGroup_iff.mp hA]
  exact Finset.mem_image_of_mem _ hv

/-- **Every molecular point group is a finite subgroup of `O(3)`.**

The point group of a molecule is by construction a subgroup of the orthogonal group `O(3)`;
the content of the theorem is that this subgroup is finite. -/
theorem point_group_finite_O3 (M : Molecule) : Finite (pointGroup M) := by
  -- A symmetry induces a self-map of the (finite) set of atoms, and is determined by it.
  have hinj : Function.Injective
      (fun A : pointGroup M => fun v : M.atoms => (⟨act A.1 v.1, act_mem_atoms A.2 v.2⟩ : M.atoms))
      := by
    intro A B hAB
    have h : ∀ v ∈ (M.atoms : Set (Fin 3 → ℝ)), act A.1 v = act B.1 v := by
      intro v hv
      have := congrFun hAB ⟨v, hv⟩
      exact congrArg Subtype.val this
    exact Subtype.ext (eq_of_mulVec_eq_of_span M.spanning h)
  exact Finite.of_injective _ hinj

/-- Molecules exist: the three atoms at the tips of the coordinate unit vectors form a genuinely
three-dimensional molecule, so the theorem above is not vacuous. -/
noncomputable example : Molecule where
  atoms := Finset.univ.image (fun i : Fin 3 => (Pi.single i 1 : Fin 3 → ℝ))
  spanning := by
    have h : ((Finset.univ.image (fun i : Fin 3 => (Pi.single i 1 : Fin 3 → ℝ)) :
          Finset (Fin 3 → ℝ)) : Set (Fin 3 → ℝ)) = Set.range ⇑(Pi.basisFun ℝ (Fin 3)) := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact congrArg Set.range (funext fun i => (Pi.basisFun_apply ℝ (Fin 3) i).symm)
    rw [h]
    exact (Pi.basisFun ℝ (Fin 3)).span_eq

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

