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

lemma kummerCharOf_isLocallyConstant (s : SeparableClosure F) :
    IsLocallyConstant (kummerCharOf s) := by
  have hopen : IsOpen ((MulAction.stabilizer (AbsGal F) s : Subgroup (AbsGal F)) :
      Set (AbsGal F)) := stabilizer_isOpen_of_isIntegral s
  have hset0 : {σ : AbsGal F | kummerCharOf s σ = 0}
      = ((MulAction.stabilizer (AbsGal F) s : Subgroup (AbsGal F)) : Set (AbsGal F)) := by
    ext σ
    simp only [Set.mem_setOf_eq, kummerCharOf_eq_zero_iff, SetLike.mem_coe,
      MulAction.mem_stabilizer_iff]
    rfl
  have hset1 : {σ : AbsGal F | kummerCharOf s σ = 1}
      = ((MulAction.stabilizer (AbsGal F) s : Subgroup (AbsGal F)) : Set (AbsGal F))ᶜ := by
    ext σ
    rw [← hset0]
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    unfold kummerCharOf
    split_ifs with h
    · simp
    · simp
  have hopen1 : IsOpen {σ : AbsGal F | kummerCharOf s σ = 1} := by
    rw [hset1]
    exact (OpenSubgroup.isClosed ⟨MulAction.stabilizer (AbsGal F) s, hopen⟩).isOpen_compl
  have hopen0 : IsOpen {σ : AbsGal F | kummerCharOf s σ = 0} := by rw [hset0]; exact hopen
  intro U
  have hval : ∀ σ : AbsGal F, kummerCharOf s σ = 0 ∨ kummerCharOf s σ = 1 := by
    intro σ
    unfold kummerCharOf
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  by_cases h0 : (0 : ZMod 2) ∈ U <;> by_cases h1 : (1 : ZMod 2) ∈ U
  · have : kummerCharOf s ⁻¹' U = Set.univ := by
      ext σ
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      rcases hval σ with h | h <;> rw [h] <;> assumption
    rw [this]; exact isOpen_univ
  · have : kummerCharOf s ⁻¹' U = {σ : AbsGal F | kummerCharOf s σ = 0} := by
      ext σ
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · intro hmem
        rcases hval σ with h | h
        · exact h
        · exact absurd (h ▸ hmem) h1
      · intro h; rw [h]; exact h0
    rw [this]; exact hopen0
  · have : kummerCharOf s ⁻¹' U = {σ : AbsGal F | kummerCharOf s σ = 1} := by
      ext σ
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · intro hmem
        rcases hval σ with h | h
        · exact absurd (h ▸ hmem) h0
        · exact h
      · intro h; rw [h]; exact h1
    rw [this]; exact hopen1
  · have : kummerCharOf s ⁻¹' U = ∅ := by
      ext σ
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      intro hmem
      rcases hval σ with h | h
      · exact h0 (h ▸ hmem)
      · exact h1 (h ▸ hmem)
    rw [this]; exact isOpen_empty

