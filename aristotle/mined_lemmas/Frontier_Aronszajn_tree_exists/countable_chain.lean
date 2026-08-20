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

/-
The limit step of the transfinite construction: at a countable limit ordinal `a`
we build a nice partial injection with domain `a` coherent with all previous ones,
by an `ω`-recursion along a cofinal sequence, reserving one new value at each stage
so that the resulting function still omits infinitely many naturals.
-/
import RequestProject.Aronszajn.Step

open Ordinal Cardinal Set

namespace Aronszajn


theorem countable_chain (C : Set TreeNode)
    (hC : ∀ x ∈ C, ∀ y ∈ C, tle x y ∨ tle y x) : C.Countable := by
  classical
  have hinjlvl : Set.InjOn tlvl C := by
    intro x hx y hy hl
    rcases hC x hx y hy with h | h
    · exact eq_of_tle_of_lvl_eq h hl
    · exact (eq_of_tle_of_lvl_eq h hl.symm).symm
  refine Set.countable_of_injective_of_countable_image hinjlvl ?_
  set L : Set Ordinal.{0} := tlvl '' C with hLdef
  set U : Set Ordinal.{0} := {e | ∃ x ∈ C, e < tlvl x} with hUdef
  -- the common extension of the chain
  set G : Ordinal.{0} → ℕ := fun e =>
    if h : ∃ x, x ∈ C ∧ e < tlvl x then (h.choose).1.2 e else 0 with hGdef
  have hGval : ∀ e, ∀ x ∈ C, e < tlvl x → G e = x.1.2 e := by
    intro e x hx he
    have hex : ∃ x, x ∈ C ∧ e < tlvl x := ⟨x, hx, he⟩
    rw [hGdef]
    simp only [dif_pos hex]
    obtain ⟨hy, hylt⟩ := hex.choose_spec
    rcases hC hex.choose hy x hx with h | h
    · exact h.2 e hylt
    · exact (h.2 e he).symm
  have hUcount : U.Countable := by
    have hinjG : Set.InjOn G U := by
      rintro e₁ ⟨x₁, hx₁, h₁⟩ e₂ ⟨x₂, hx₂, h₂⟩ hEq
      rcases hC x₁ hx₁ x₂ hx₂ with h | h
      · have h₁' : e₁ < tlvl x₂ := lt_of_lt_of_le h₁ h.1
        rw [hGval e₁ x₂ hx₂ h₁', hGval e₂ x₂ hx₂ h₂] at hEq
        exact injBelow_node x₂ e₁ h₁' e₂ h₂ hEq
      · have h₂' : e₂ < tlvl x₁ := lt_of_lt_of_le h₂ h.1
        rw [hGval e₁ x₁ hx₁ h₁, hGval e₂ x₁ hx₁ h₂'] at hEq
        exact injBelow_node x₁ e₁ h₁ e₂ h₂' hEq
    exact Set.countable_of_injective_of_countable_image hinjG (Set.to_countable _)
  have hsub : (L \ U).Subsingleton := by
    intro b hb c hc
    have hble : b ≤ c := by
      obtain ⟨x, hx, rfl⟩ := hb.1
      by_contra hlt
      exact hc.2 ⟨x, hx, lt_of_not_ge hlt⟩
    have hcle : c ≤ b := by
      obtain ⟨x, hx, rfl⟩ := hc.1
      by_contra hlt
      exact hb.2 ⟨x, hx, lt_of_not_ge hlt⟩
    exact le_antisymm hble hcle
  refine (hUcount.union hsub.countable).mono ?_
  intro b hb
  by_cases h : b ∈ U
  · exact Or.inl h
  · exact Or.inr ⟨hb, h⟩

end Aronszajn

/-
Basic definitions for the construction of an Aronszajn tree.

A "node" of the tree we build is a function `f : Ordinal → ℕ` which is injective
below some countable ordinal `a` and vanishes from `a` on.
-/
import Mathlib

open Ordinal Cardinal Set

namespace Aronszajn

/-- `f` vanishes from `a` on. -/
