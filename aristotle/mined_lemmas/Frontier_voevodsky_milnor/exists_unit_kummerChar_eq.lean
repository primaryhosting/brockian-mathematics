import Mathlib

/-!
# Voevodsky Milnor: definitions and supporting results

Supporting development for `Frontier.voevodsky_milnor` (see `RequestProject/Main.lean`):
mod-2 Milnor K-theory, mod-2 Galois cohomology, the statement of the Milnor conjecture, the
degree-zero base case, the separably closed case, and the degree-one identifications.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false

namespace Frontier

/-!
## Mod-2 Milnor K-theory

For a field `F`, the `n`-th Milnor K-group `K^M_n(F)` is the degree-`n` part of the quotient of
the tensor algebra of the abelian group `Fˣ` by the Steinberg relations `a ⊗ (1 - a) = 0`.
Reducing mod 2, `k^M_n(F) = K^M_n(F)/2` is therefore the quotient of the free `ZMod 2`-module on
`n`-tuples of units by
* multilinearity in each slot, and
* the Steinberg relations (in adjacent slots).

This is the definition used below.
-/

section Milnor

variable (F : Type) [Field F]

/-- The defining relations of mod-2 Milnor K-theory in degree `n`: multilinearity in each slot,
and the Steinberg relation `{a, 1 - a} = 0` in adjacent slots. -/

lemma exists_unit_kummerChar_eq (h2 : (2 : F) ≠ 0) (χ : contHom1 F)
    (hne : (χ : AbsGal F → ZMod 2) ≠ 0) :
    ∃ a : Fˣ, kummerChar h2 a = (χ : AbsGal F → ZMod 2) := by
  have hopen := ker_charHom_isOpen χ
  have hclosed : IsClosed (((charHom χ).ker : Subgroup (AbsGal F)) : Set (AbsGal F)) :=
    OpenSubgroup.isClosed ⟨(charHom χ).ker, hopen⟩
  let Hc : ClosedSubgroup (AbsGal F) := ⟨(charHom χ).ker, hclosed⟩
  have hfix : (IntermediateField.fixedField ((charHom χ).ker)).fixingSubgroup
      = (charHom χ).ker := InfiniteGalois.fixingSubgroup_fixedField Hc
  have hrank : Module.finrank F (IntermediateField.fixedField ((charHom χ).ker)) = 2 := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index, hfix]
    exact ker_charHom_index χ hne
  obtain ⟨y, hyL, hyb, c, hc⟩ :=
    exists_generator_sq_mem h2 (IntermediateField.fixedField ((charHom χ).ker)) hrank
  have hadj : IntermediateField.adjoin F {y} = IntermediateField.fixedField ((charHom χ).ker) :=
    adjoin_eq_of_finrank_two hrank hyL hyb
  have hy0 : y ≠ 0 := by
    intro h
    exact hyb (h ▸ zero_mem _)
  have hc0 : c ≠ 0 := by
    intro h
    apply hy0
    have hy2 : y ^ 2 = 0 := by rw [hc, h, map_zero]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hy2
  refine ⟨Units.mk0 c hc0, ?_⟩
  have hsq : (kummerRoot h2 (Units.mk0 c hc0)) ^ 2 = y ^ 2 := by
    rw [kummerRoot_sq, hc]
    simp
  rw [kummerChar, kummerCharOf_eq_of_sq_eq hsq]
  funext σ
  have hiff : σ y = y ↔ (χ : AbsGal F → ZMod 2) σ = 0 := by
    constructor
    · intro h
      have hmem : σ ∈ (IntermediateField.adjoin F {y}).fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        exact (IntermediateField.forall_mem_adjoin_smul_eq_self_iff F σ).2
          (by rintro w rfl; exact h)
      rw [hadj, hfix] at hmem
      exact (mem_ker_charHom_iff χ σ).1 hmem
    · intro h
      have hmem : σ ∈ (charHom χ).ker := (mem_ker_charHom_iff χ σ).2 h
      rw [← hfix, IntermediateField.mem_fixingSubgroup_iff] at hmem
      exact hmem y hyL
  have hval : kummerCharOf y σ = 0 ∨ kummerCharOf y σ = 1 := by
    unfold kummerCharOf
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases char_eq_zero_or_one χ σ with h | h
  · rw [h]
    exact (kummerCharOf_eq_zero_iff y σ).2 (hiff.2 h)
  · rcases hval with hv | hv
    · exfalso
      have hz := hiff.1 ((kummerCharOf_eq_zero_iff y σ).1 hv)
      rw [hz] at h
      exact absurd h (by decide)
    · rw [hv, h]

