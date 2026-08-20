import Mathlib

/-!
# Mod-2 Milnor K-theory of a field

For a field `F` we define
`k_n(F) = K^M_n(F)/2`, the `n`-th mod-2 Milnor K-group, as the quotient of the `n`-fold
tensor power over `𝔽₂` of the square class group `F^×/(F^×)²` by the Steinberg relations
`{a, 1-a} = 0`.
-/

open scoped TensorProduct

namespace MilnorK

variable (F : Type) [Field F]

/-- The subgroup of squares of `Fˣ`. -/

theorem exists_chiU_eq (f : GalF F → ZMod 2) (hcont : Continuous f)
    (hf : ∀ σ τ : GalF F, f (σ * τ) = f σ + f τ) : ∃ a : Fˣ, ∀ σ, f σ = chiU a σ := by
  by_cases hzero : ∀ σ, f σ = 0
  · exact ⟨1, fun σ => by rw [hzero σ, chiU_one]⟩
  push_neg at hzero
  obtain ⟨σ₀, hσ₀⟩ := hzero
  have hσ₀₁ : f σ₀ = 1 := by revert hσ₀; generalize f σ₀ = v; revert v; decide
  have hf1 : f 1 = 0 := by
    have h := hf 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  let H : Subgroup (GalF F) :=
    { carrier := {σ | f σ = 0}
      one_mem' := hf1
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [hf, hx, hy, add_zero]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        have h := hf x x⁻¹
        rw [mul_inv_cancel, hf1, hx, zero_add] at h
        exact h.symm }
  have hmemH : ∀ σ : GalF F, σ ∈ H ↔ f σ = 0 := fun _ => Iff.rfl
  have hHopen : IsOpen (H : Set (GalF F)) := hcont.isOpen_preimage {0} (isOpen_discrete _)
  have hHclosed : IsClosed (H : Set (GalF F)) := (OpenSubgroup.mk H hHopen).isClosed
  have hidx : H.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨σ₀, fun b => ?_⟩
    have hb : f (b * σ₀) = f b + 1 := by rw [hf, hσ₀₁]
    rw [Xor', hmemH, hmemH, hb]
    generalize f b = v
    revert v
    decide
  have hfixL : (fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHclosed⟩
  have hrank : Module.finrank F (fixedField H) = 2 := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (fixedField H), hfixL]
    exact hidx
  obtain ⟨y, hyL, hybot, a₀, hy2⟩ := exists_sqrt_of_finrank_two (fixedField H) hrank
  have ha₀ : a₀ ≠ 0 := by
    intro h
    rw [h, map_zero, mul_self_eq_zero] at hy2
    exact hybot (hy2 ▸ zero_mem _)
  refine ⟨Units.mk0 a₀ ha₀, fun σ => ?_⟩
  have hroot : y * y = algebraMap F (Ksep F) ((Units.mk0 a₀ ha₀ : Fˣ) : F) := hy2
  have hchi : chi ((Units.mk0 a₀ ha₀ : Fˣ) : F) σ = 0 ↔ σ y = y :=
    chi_eq_zero_iff_of_root hroot σ
  haveI : FiniteDimensional F (fixedField H) :=
    Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
  have hFy : F⟮ y ⟯ = fixedField H := by
    haveI : FiniteDimensional F F⟮ y ⟯ :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
    have hne1 : Module.finrank F F⟮ y ⟯ ≠ 1 := by
      intro h
      rw [IntermediateField.finrank_eq_one_iff] at h
      exact hybot (h ▸ IntermediateField.mem_adjoin_simple_self F y)
    have hpos : 0 < Module.finrank F F⟮ y ⟯ := Module.finrank_pos
    exact IntermediateField.eq_of_le_of_finrank_le
      (IntermediateField.adjoin_simple_le_iff.2 hyL) (by rw [hrank]; omega)
  have hHy : σ ∈ H ↔ σ y = y := by
    rw [← hfixL, ← hFy]
    constructor
    · intro h
      rw [IntermediateField.mem_fixingSubgroup_iff] at h
      exact h y (IntermediateField.mem_adjoin_simple_self F y)
    · intro h
      rw [IntermediateField.mem_fixingSubgroup_iff]
      have hall := (IntermediateField.forall_mem_adjoin_smul_eq_self_iff (F := F) (S := {y}) σ).2
        (by rintro z (rfl : z = y); exact h)
      exact fun x hx => hall x hx
  by_cases hσH : σ ∈ H
  · rw [(hmemH σ).1 hσH, chiU, hchi.2 (hHy.1 hσH)]
  · have h1 : f σ = 1 := by
      have hne : f σ ≠ 0 := hσH
      revert hne; generalize f σ = v; revert v; decide
    have h2 : chiU (Units.mk0 a₀ ha₀) σ = 1 := by
      have hne : chi ((Units.mk0 a₀ ha₀ : Fˣ) : F) σ ≠ 0 := fun h => hσH (hHy.2 (hchi.1 h))
      rw [chiU]
      revert hne; generalize chi ((Units.mk0 a₀ ha₀ : Fˣ) : F) σ = v; revert v; decide
    rw [h1, h2]

variable (F)

/-- The Kummer map on square classes, as a function. -/
