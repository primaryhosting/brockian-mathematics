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
def act (A : O3) (x : Fin 3 → ℝ) : Fin 3 → ℝ := (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x

@[simp] lemma act_one (x : Fin 3 → ℝ) : act 1 x = x := by
  simp [act]

lemma act_mul (A B : O3) (x : Fin 3 → ℝ) : act (A * B) x = act A (act B x) := by
  simp [act, Matrix.mulVec_mulVec]

/-- The point group of a molecule with nuclear positions `S`: all orthogonal
transformations of `ℝ³` carrying the molecule onto itself. -/
def pointGroup (S : Set (Fin 3 → ℝ)) : Subgroup O3 where
  carrier := {A | act A '' S = S}
  mul_mem' := by
    intro A B hA hB
    simp only [Set.mem_setOf_eq] at *
    have h : act (A * B) '' S = act A '' (act B '' S) := by
      rw [Set.image_image]
      exact Set.image_congr' (fun x => act_mul A B x)
    rw [h, hB, hA]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [show (act 1 : (Fin 3 → ℝ) → (Fin 3 → ℝ)) = id from funext (fun x => act_one x)]
    exact Set.image_id S
  inv_mem' := by
    intro A hA
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hA]
    rw [Set.image_image]
    have h : (fun x => act A⁻¹ (act A x)) = id := by
      funext x
      rw [← act_mul, inv_mul_cancel, act_one, id]
    rw [h, Set.image_id]

lemma mem_pointGroup {S : Set (Fin 3 → ℝ)} {A : O3} :
    A ∈ pointGroup S ↔ act A '' S = S := Iff.rfl

/-- **Every molecular point group is a finite subgroup of `O(3)`.**

For a molecule with a finite set `S` of nuclear positions spanning `ℝ³`, the point
group `Chem.pointGroup S` — a subgroup of `O(3)` by construction — is finite. -/
theorem point_group_finite_O3 (S : Set (Fin 3 → ℝ)) (hfin : S.Finite)
    (hspan : Submodule.span ℝ S = ⊤) : Finite (pointGroup S) := by
  have : Fintype S := hfin.fintype
  -- An element of the point group is determined by its restriction to `S`, since `S` spans.
  have key : ∀ A B : pointGroup S, (∀ x ∈ S, act A.1 x = act B.1 x) → A = B := by
    intro A B h
    have hlin : Matrix.toLin' (A.1 : Matrix (Fin 3) (Fin 3) ℝ)
        = Matrix.toLin' (B.1 : Matrix (Fin 3) (Fin 3) ℝ) := by
      refine LinearMap.ext_on hspan (fun x hx => ?_)
      simpa [Matrix.toLin'_apply, act] using h x hx
    exact Subtype.ext (Subtype.ext (Matrix.toLin'.injective hlin))
  -- The restriction lands in `S`.
  have himg : ∀ (A : pointGroup S) (x : S), act A.1 x.1 ∈ S := by
    intro A x
    have hA : act A.1 '' S = S := mem_pointGroup.mp A.2
    exact hA.subset ⟨x.1, x.2, rfl⟩
  let F : pointGroup S → (S → S) := fun A x => ⟨act A.1 x.1, himg A x⟩
  have hF : Function.Injective F := by
    intro A B hAB
    exact key A B (fun x hx => congrArg Subtype.val (congrFun hAB ⟨x, hx⟩))
  exact Finite.of_injective F hF

/-!
### The spanning hypothesis is necessary

A linear molecule (here a diatomic aligned with the `z`-axis) is invariant under every
rotation about that axis, so its point group is infinite.
-/

/-- Rotation by `θ` about the `z`-axis, as an element of `O(3)`. -/
noncomputable def rotZ (θ : ℝ) : O3 :=
  ⟨!![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1], by
    rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf <;> simp [Real.sin_sq_add_cos_sq]⟩

/-- The nuclear positions of a diatomic molecule aligned with the `z`-axis. -/
def diatomic : Set (Fin 3 → ℝ) := {![0, 0, 1], ![0, 0, -1]}

lemma rotZ_mem (θ : ℝ) : rotZ θ ∈ pointGroup diatomic := by
  show act (rotZ θ) '' diatomic = diatomic
  have h1 : act (rotZ θ) ![0, 0, 1] = ![0, 0, 1] := by
    funext i; fin_cases i <;> simp [act, rotZ, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have h2 : act (rotZ θ) ![0, 0, -1] = ![0, 0, -1] := by
    funext i; fin_cases i <;> simp [act, rotZ, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  simp [diatomic, Set.image_insert_eq, h1, h2]

/-- The point group of a linear molecule is infinite, so the spanning hypothesis in
`Chem.point_group_finite_O3` cannot be dropped. -/
theorem pointGroup_diatomic_infinite : Infinite (pointGroup diatomic) := by
  have hinj : Function.Injective
      (fun n : ℕ => (⟨rotZ (1 / (n + 1)), rotZ_mem _⟩ : pointGroup diatomic)) := by
    intro n m h
    have h' : Real.cos (1 / ((n : ℝ) + 1)) = Real.cos (1 / ((m : ℝ) + 1)) := by
      have h2 := congrArg
        (fun A : pointGroup diatomic => ((A : O3) : Matrix (Fin 3) (Fin 3) ℝ) 0 0) h
      simpa [rotZ] using h2
    have hb : ∀ k : ℕ, (1 : ℝ) / (k + 1) ∈ Set.Icc 0 Real.pi := by
      intro k
      refine ⟨by positivity, ?_⟩
      have h1 : (1 : ℝ) / (k + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; simp
      linarith [Real.pi_gt_three]
    have heq := Real.injOn_cos (hb n) (hb m) h'
    have hnm : (n : ℝ) = m := by field_simp at heq; linarith
    exact_mod_cast hnm
  exact Infinite.of_injective _ hinj

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

