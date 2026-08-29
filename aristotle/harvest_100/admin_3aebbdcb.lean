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

A molecule is modelled as a finite set `S` of atomic positions in `ℝ³` (for a molecule
with several atomic species one takes `S` to be the positions of the atoms of one species,
or one works with the labelled version; the argument is identical).

Its *point group* is the set of orthogonal transformations of `ℝ³` mapping the molecule onto
itself.  By construction this is a subgroup of `O(3)`; the content of the theorem is that it
is *finite*, which holds exactly when the molecule is not linear, i.e. when the atomic
positions span `ℝ³`.  (For a linear molecule the point group is `C∞v` or `D∞h`, which is
infinite, so the spanning hypothesis cannot be dropped.)
-/

namespace Chem

open Matrix

/-- The orthogonal group `O(3)`, realised as the group of real orthogonal `3 × 3` matrices. -/
abbrev O3 : Submonoid (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.orthogonalGroup (Fin 3) ℝ

/-- The action of an element of `O(3)` on a point of `ℝ³`. -/
def act (A : O3) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (A : Matrix (Fin 3) (Fin 3) ℝ).mulVec x

theorem act_injective (A : O3) : Function.Injective (act A) :=
  Matrix.mulVec_injective_of_isUnit Unitary.isUnit_coe

theorem act_one (x : Fin 3 → ℝ) : act 1 x = x := by
  simp [act]

theorem act_mul (A B : O3) (x : Fin 3 → ℝ) : act (A * B) x = act A (act B x) := by
  simp [act, Submonoid.coe_mul, Matrix.mulVec_mulVec]

theorem act_inv_act (A : O3) (x : Fin 3 → ℝ) : act A⁻¹ (act A x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one]

/-- An orthogonal transformation preserving a finite set of points maps that set *onto*
itself, hence so does its inverse. -/
theorem inv_mapsTo_of_mapsTo {S : Finset (Fin 3 → ℝ)} {A : O3}
    (hA : ∀ x ∈ S, act A x ∈ S) : ∀ x ∈ S, act A⁻¹ x ∈ S := by
  classical
  have himg : S.image (act A) = S := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      simp only [Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hA x hx
    · exact le_of_eq (Finset.card_image_of_injective S (act_injective A)).symm
  intro x hx
  rw [← himg] at hx
  simp only [Finset.mem_image] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rw [← hyx, act_inv_act]
  exact hy

/-- The **point group** of a molecule whose atoms sit at the (finitely many) positions `S`:
the subgroup of `O(3)` consisting of the orthogonal transformations that map the set of
atomic positions onto itself. -/
def pointGroup (S : Finset (Fin 3 → ℝ)) : Subgroup O3 where
  carrier := {A | ∀ x ∈ S, act A x ∈ S}
  one_mem' := by intro x hx; rwa [act_one]
  mul_mem' := by
    intro A B hA hB x hx
    rw [act_mul]
    exact hA _ (hB x hx)
  inv_mem' := by
    intro A hA
    exact inv_mapsTo_of_mapsTo hA

@[simp] theorem mem_pointGroup {S : Finset (Fin 3 → ℝ)} {A : O3} :
    A ∈ pointGroup S ↔ ∀ x ∈ S, act A x ∈ S := Iff.rfl

/-- Two orthogonal transformations agreeing on a spanning set are equal. -/
theorem eq_of_act_eq_on_span {S : Finset (Fin 3 → ℝ)}
    (hspan : Submodule.span ℝ (S : Set (Fin 3 → ℝ)) = ⊤) {A B : O3}
    (h : ∀ x ∈ S, act A x = act B x) : A = B := by
  have hlin : Matrix.toLin' (A : Matrix (Fin 3) (Fin 3) ℝ)
      = Matrix.toLin' (B : Matrix (Fin 3) (Fin 3) ℝ) := by
    refine LinearMap.ext_on hspan ?_
    intro x hx
    simpa [Matrix.toLin'_apply, act] using h x hx
  have : (A : Matrix (Fin 3) (Fin 3) ℝ) = (B : Matrix (Fin 3) (Fin 3) ℝ) :=
    Matrix.toLin'.injective hlin
  exact Subtype.ext this

/-- **Every molecular point group is a finite subgroup of `O(3)`.**

For a molecule given by a finite set `S` of atomic positions spanning `ℝ³` (i.e. a
non-linear molecule), the point group `pointGroup S` is, by construction, a subgroup of the
orthogonal group `O(3)`, and it is finite. -/
theorem point_group_finite_O3 (S : Finset (Fin 3 → ℝ))
    (hspan : Submodule.span ℝ (S : Set (Fin 3 → ℝ)) = ⊤) :
    Finite (pointGroup S) := by
  classical
  -- restriction of the action gives an injection of the point group into `S → S`
  have hinj : Function.Injective
      (fun A : pointGroup S => fun x : S => (⟨act (A : O3) x, A.2 x x.2⟩ : S)) := by
    intro A B hAB
    have h : ∀ x ∈ S, act (A : O3) x = act (B : O3) x := by
      intro x hx
      have := congrFun hAB ⟨x, hx⟩
      simpa using congrArg Subtype.val this
    exact Subtype.ext (eq_of_act_eq_on_span hspan h)
  exact Finite.of_injective _ hinj

/-- Non-vacuity: there really are molecules satisfying the hypothesis, e.g. three atoms placed
along three orthogonal axes. -/
theorem exists_spanning_atoms :
    ∃ S : Finset (Fin 3 → ℝ), Submodule.span ℝ (S : Set (Fin 3 → ℝ)) = ⊤ := by
  classical
  refine ⟨Finset.image (fun i : Fin 3 => Pi.single i (1 : ℝ)) Finset.univ, ?_⟩
  have hb := (Pi.basisFun ℝ (Fin 3)).span_eq
  convert hb using 2
  ext x
  simp [Set.range, Pi.basisFun_apply, eq_comm]

/-- Consequently there is at least one (finite) molecular point group. -/
example : ∃ S : Finset (Fin 3 → ℝ), Finite (pointGroup S) := by
  obtain ⟨S, hS⟩ := exists_spanning_atoms
  exact ⟨S, point_group_finite_O3 S hS⟩

/-! ### Sharpness: the non-linearity (spanning) hypothesis cannot be dropped

A linear molecule, modelled here by a single atom on the `z`-axis, is invariant under all
rotations about that axis, so its point group (`C∞v`) is infinite. -/

/-- The rotation of `ℝ³` by the angle `t` about the `z`-axis. -/
noncomputable def rotZ (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos t, -Real.sin t, 0; Real.sin t, Real.cos t, 0; 0, 0, 1]

theorem rotZ_mem_O3 (t : ℝ) : rotZ t ∈ O3 := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.mul_apply, Fin.sum_univ_three] <;> ring_nf <;>
    simp [Real.sin_sq_add_cos_sq, Real.cos_sq_add_sin_sq]

theorem act_rotZ_zAxis (t : ℝ) :
    act ⟨rotZ t, rotZ_mem_O3 t⟩ (Pi.single 2 (1 : ℝ)) = Pi.single 2 (1 : ℝ) := by
  funext i
  fin_cases i <;> simp [act, rotZ, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The point group of a linear molecule is infinite, so the spanning (non-linearity)
hypothesis in `point_group_finite_O3` cannot be removed. -/
theorem linear_molecule_point_group_infinite :
    Infinite (pointGroup ({Pi.single 2 (1 : ℝ)} : Finset (Fin 3 → ℝ))) := by
  have hmem : ∀ t : ℝ, (⟨rotZ t, rotZ_mem_O3 t⟩ : O3) ∈
      pointGroup ({Pi.single 2 (1 : ℝ)} : Finset (Fin 3 → ℝ)) := by
    intro t x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    rw [Finset.mem_singleton, act_rotZ_zAxis]
  refine Infinite.of_injective
    (fun n : ℕ => (⟨⟨rotZ (1 / (n + 1)), rotZ_mem_O3 _⟩, hmem _⟩ :
      pointGroup ({Pi.single 2 (1 : ℝ)} : Finset (Fin 3 → ℝ)))) ?_
  intro n m hnm
  have h : rotZ (1 / ((n : ℝ) + 1)) = rotZ (1 / ((m : ℝ) + 1)) := by
    simpa using Subtype.ext_iff.mp (Subtype.ext_iff.mp hnm)
  have h1 : Real.cos (1 / ((n : ℝ) + 1)) = Real.cos (1 / ((m : ℝ) + 1)) := by
    have := congrFun (congrFun h 0) 0
    simpa [rotZ] using this
  have hb : ∀ k : ℕ, (1 : ℝ) / (k + 1) ∈ Set.Icc 0 Real.pi := by
    intro k
    refine ⟨by positivity, ?_⟩
    have h2 : (1 : ℝ) / (k + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    linarith [Real.pi_gt_three]
  have heq := Real.injOn_cos (hb n) (hb m) h1
  have hpos : (0 : ℝ) < (n + 1) := by positivity
  have hpos' : (0 : ℝ) < (m + 1) := by positivity
  have hsucc : ((n : ℝ) + 1) = ((m : ℝ) + 1) := by
    field_simp at heq
    linarith
  have : (n : ℝ) = m := by linarith
  exact_mod_cast this

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

