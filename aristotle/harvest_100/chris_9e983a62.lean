/-
# Point Group Finite O 3
Category: Chemistry
Target: Chem.point_group_finite_O3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix

/-- The orthogonal group `O(3)`, realized as the group of `3 × 3` real orthogonal matrices. -/
abbrev O3 : Submonoid (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.orthogonalGroup (Fin 3) ℝ

/-- The **molecular point group** of a molecule whose nuclei occupy the finite set of
positions `S ⊆ ℝ³` (with the centre of mass at the origin): the subgroup of `O(3)`
consisting of those orthogonal transformations that map the set of nuclear positions
onto itself. -/
def pointGroup (S : Finset (Fin 3 → ℝ)) : Subgroup ↥O3 where
  carrier := {M | ∀ v, (M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v ∈ S ↔ v ∈ S}
  mul_mem' := by
    intro M N hM hN v
    have h : ((M * N : ↥O3) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v
        = (M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ((N : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) := by
      rw [Matrix.mulVec_mulVec]
      rfl
    rw [h, hM, hN]
  one_mem' := by
    intro v
    have h : ((1 : ↥O3) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v = v := by
      rw [show ((1 : ↥O3) : Matrix (Fin 3) (Fin 3) ℝ) = 1 from rfl, Matrix.one_mulVec]
    rw [h]
  inv_mem' := by
    intro M hM v
    have hMM : ((M * M⁻¹ : ↥O3) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
      rw [mul_inv_cancel]; rfl
    have h : (M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ((M⁻¹ : ↥O3) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, show (M : Matrix (Fin 3) (Fin 3) ℝ) * (M⁻¹ : ↥O3)
        = ((M * M⁻¹ : ↥O3) : Matrix (Fin 3) (Fin 3) ℝ) from rfl, hMM, Matrix.one_mulVec]
    have := hM ((M⁻¹ : ↥O3) *ᵥ v)
    rw [h] at this
    exact this.symm

/-- Elements of a point group map nuclear positions to nuclear positions. -/
theorem pointGroup_mapsTo {S : Finset (Fin 3 → ℝ)} {M : ↥O3} (hM : M ∈ pointGroup S)
    {v : Fin 3 → ℝ} (hv : v ∈ S) : (M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v ∈ S :=
  (hM v).2 hv

/-- **Every molecular point group is a finite subgroup of `O(3)`.**

By construction `Chem.pointGroup S` is a subgroup of the orthogonal group `O(3)`; the content
of the statement is that it is *finite*, whenever the nuclear positions `S` are finitely many
and are not all contained in a proper subspace of `ℝ³` (i.e. they span `ℝ³`, which holds for
any genuinely three-dimensional molecule).  Indeed, a symmetry operation is determined by its
action on a spanning set, so restriction gives an injection of the point group into the
(finite) set of self-maps of the nuclear positions. -/
theorem point_group_finite_O3 (S : Finset (Fin 3 → ℝ))
    (hspan : Submodule.span ℝ (S : Set (Fin 3 → ℝ)) = ⊤) :
    Finite (pointGroup S) := by
  have hinj : Function.Injective
      (fun M : pointGroup S => fun v : (S : Set (Fin 3 → ℝ)) =>
        (⟨(M.1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (v : Fin 3 → ℝ),
          pointGroup_mapsTo M.2 v.2⟩ : (S : Set (Fin 3 → ℝ)))) := by
    intro M N hMN
    have hEqOn : Set.EqOn ⇑(Matrix.mulVecLin (M.1 : Matrix (Fin 3) (Fin 3) ℝ))
        ⇑(Matrix.mulVecLin (N.1 : Matrix (Fin 3) (Fin 3) ℝ)) (S : Set (Fin 3 → ℝ)) := by
      intro v hv
      have := congrFun hMN ⟨v, hv⟩
      simpa [Matrix.mulVecLin_apply] using congrArg Subtype.val this
    have hlin : Matrix.mulVecLin (M.1 : Matrix (Fin 3) (Fin 3) ℝ)
        = Matrix.mulVecLin (N.1 : Matrix (Fin 3) (Fin 3) ℝ) :=
      LinearMap.ext_on hspan hEqOn
    have hmat : (M.1 : Matrix (Fin 3) (Fin 3) ℝ) = (N.1 : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [Matrix.ext_iff_mulVec]
      intro v
      simpa [Matrix.mulVecLin_apply] using congrArg (fun f => f v) (congrArg DFunLike.coe hlin)
    exact Subtype.ext (Subtype.ext hmat)
  exact Finite.of_injective _ hinj

/-! ### A concrete example: the hypotheses are satisfiable and the point group can be nontrivial -/

/-- The six nuclear positions `±e₁, ±e₂, ±e₃` (e.g. the ligands of an octahedral molecule). -/
noncomputable def octahedralAxes : Finset (Fin 3 → ℝ) :=
  {Pi.single 0 1, Pi.single 1 1, Pi.single 2 1,
   -Pi.single 0 1, -Pi.single 1 1, -Pi.single 2 1}

/-- The octahedral positions span `ℝ³`, so the finiteness theorem applies to them. -/
theorem span_octahedralAxes :
    Submodule.span ℝ ((octahedralAxes : Finset (Fin 3 → ℝ)) : Set (Fin 3 → ℝ)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin 3)).span_eq, Submodule.span_le]
  rintro x hx
  simp only [Set.mem_range, Pi.basisFun_apply] at hx
  obtain ⟨i, rfl⟩ := hx
  apply Submodule.subset_span
  fin_cases i <;> simp [octahedralAxes]

/-- The inversion `-1` is an orthogonal transformation. -/
theorem neg_one_mem_O3 : (-1 : Matrix (Fin 3) (Fin 3) ℝ) ∈ O3 := by
  rw [Matrix.mem_orthogonalGroup_iff]
  simp

/-- The inversion centre belongs to the point group of the octahedral positions, so this
point group is nontrivial (in particular the finiteness statement is not vacuous). -/
theorem inversion_mem_pointGroup_octahedralAxes :
    (⟨-1, neg_one_mem_O3⟩ : ↥O3) ∈ pointGroup octahedralAxes := by
  intro v
  have hv : ((⟨-1, neg_one_mem_O3⟩ : ↥O3) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v = -v := by
    simp [Matrix.neg_mulVec]
  rw [hv]
  simp only [octahedralAxes, Finset.mem_insert, Finset.mem_singleton, neg_eq_iff_eq_neg, neg_neg]
  tauto

/-- The point group of the octahedral positions is a nontrivial finite subgroup of `O(3)`. -/
theorem pointGroup_octahedralAxes_nontrivial :
    (⟨-1, neg_one_mem_O3⟩ : ↥O3) ≠ 1 := by
  intro h
  have h' : (-1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := congrArg Subtype.val h
  have := congrFun (congrFun h' 0) 0
  norm_num [Matrix.one_apply] at this

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

