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

/-!
# Existence of an Aronszajn tree

An *Aronszajn tree* is a tree of height `ω₁` all of whose levels are countable and which has no
uncountable chain (equivalently, no uncountable branch).

We construct one in the classical way, from a *coherent sequence* of finite-to-one functions
`E α : α → ℕ` (`α < ω₁`), built by transfinite recursion: `E α` is finite-to-one on `α`, and for
`β < α` the functions `E α ↾ β` and `E β` differ at only finitely many places.  The tree consists
of all pairs `(α, f)` with `α < ω₁` and `f : α → ℕ` differing from `E α` at only finitely many
places, ordered by end-extension.
-/

namespace Frontier

open Ordinal Cardinal Set

/-! ### Countability and `ω₁` -/


theorem E_main (α : Ordinal.{0}) (hα : α < ω₁) :
    (∀ k, {ξ | ξ < α ∧ E α ξ = k}.Finite) ∧
      (∀ β < α, {ξ | ξ < β ∧ E α ξ ≠ E β ξ}.Finite) := by
  revert hα
  induction α using Ordinal.induction with
  | _ α ih =>
  intro hα
  rcases eq_or_ne α 0 with rfl | hα0
  · refine ⟨fun k => ?_, fun β hβ => absurd hβ (by simp)⟩
    have : {ξ : Ordinal.{0} | ξ < 0 ∧ E 0 ξ = k} = ∅ := by
      ext ξ; simp
    rw [this]
    exact Set.finite_empty
  by_cases hl : Order.IsSuccLimit α
  · -- limit case
    obtain ⟨h0, hmono, hlt, hcof⟩ := ladder_spec hα hl
    have ihl : ∀ n : ℕ, (∀ k, {ξ | ξ < ladder α (n + 1) ∧ E (ladder α (n + 1)) ξ = k}.Finite) ∧
        (∀ β < ladder α (n + 1),
          {ξ | ξ < β ∧ E (ladder α (n + 1)) ξ ≠ E β ξ}.Finite) := fun n =>
      ih _ (hlt (n + 1)) ((hlt (n + 1)).trans hα)
    constructor
    · -- finite fibers
      intro k
      have hsub : {ξ : Ordinal.{0} | ξ < α ∧ E α ξ = k} ⊆
          ⋃ j ∈ Set.Iic k,
            {ξ : Ordinal.{0} | ξ < ladder α (j + 1) ∧ E (ladder α (j + 1)) ξ ≤ k} := by
        rintro ξ ⟨hξ, hk⟩
        obtain ⟨m, hm1, -, hm3⟩ := E_limit_block hα hl hξ
        rw [hm3] at hk
        exact Set.mem_biUnion (Set.mem_Iic.mpr (le_of_max_le_right hk.le))
          ⟨hm1, le_of_max_le_left hk.le⟩
      refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iic k) (fun j _ => ?_)) hsub
      exact finite_of_le (ihl j).1 k
    · -- coherence
      intro β hβ
      obtain ⟨n, hn⟩ := hcof β hβ
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [h0] at hn
        simp at hn
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      set γ : Ordinal.{0} := ladder α (n + 1) with hγ
      have hγα : γ < α := hlt _
      have hγω : γ < ω₁ := hγα.trans hα
      have hstep1 : {ξ : Ordinal.{0} | ξ < γ ∧ E α ξ ≠ E γ ξ}.Finite := by
        have hsub : {ξ : Ordinal.{0} | ξ < γ ∧ E α ξ ≠ E γ ξ} ⊆
            ⋃ j ∈ Set.Iio (n + 1),
              ({ξ : Ordinal.{0} | ξ < ladder α (j + 1) ∧ E (ladder α (j + 1)) ξ ≠ E γ ξ} ∪
                {ξ : Ordinal.{0} | ξ < ladder α (j + 1) ∧ E (ladder α (j + 1)) ξ ≤ j}) := by
          rintro ξ ⟨hξγ, hne⟩
          have hξα : ξ < α := hξγ.trans hγα
          obtain ⟨m, hm1, hm2, hm3⟩ := E_limit_block hα hl hξα
          have hmn : m < n + 1 := Nat.lt_succ_of_le (hm2 n hξγ)
          refine Set.mem_biUnion (Set.mem_Iio.mpr hmn) ?_
          by_cases heq : E (ladder α (m + 1)) ξ = E γ ξ
          · refine Or.inr ⟨hm1, ?_⟩
            rw [hm3, heq] at hne
            omega
          · exact Or.inl ⟨hm1, heq⟩
        refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iio (n + 1)) (fun j hj => ?_)) hsub
        refine Set.Finite.union ?_ (finite_of_le (ihl j).1 j)
        rcases eq_or_lt_of_le (hmono (by have := Set.mem_Iio.mp hj; omega : j + 1 ≤ n + 1)) with heq | hlt'
        · have : {ξ : Ordinal.{0} | ξ < ladder α (j + 1) ∧ E (ladder α (j + 1)) ξ ≠ E γ ξ} = ∅ := by
            ext ξ
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
            intro _
            rw [← hγ] at heq
            rw [heq]
          rw [this]; exact Set.finite_empty
        · have hfin := ((ih γ hγα hγω).2) (ladder α (j + 1)) hlt'
          refine Set.Finite.subset hfin (fun ξ hξ => ⟨hξ.1, ?_⟩)
          exact fun hcontra => hξ.2 hcontra.symm
      have hstep2 : {ξ : Ordinal.{0} | ξ < β ∧ E γ ξ ≠ E β ξ}.Finite :=
        ((ih γ hγα hγω).2) β hn
      refine Set.Finite.subset (hstep1.union hstep2) ?_
      rintro ξ ⟨hξβ, hne⟩
      by_cases hc : E α ξ = E γ ξ
      · exact Or.inr ⟨hξβ, fun h => hne (hc.trans h)⟩
      · exact Or.inl ⟨hξβ.trans hn, hc⟩
  · -- successor case
    obtain ⟨β, rfl⟩ : ∃ β : Ordinal.{0}, α = Order.succ β := by
      rw [Order.not_isSuccLimit_iff] at hl
      rcases hl with h | h
      · exact absurd (nonpos_iff_eq_zero.mp (h (_root_.zero_le α))) hα0
      · rw [Order.not_isSuccPrelimit_iff] at h
        obtain ⟨b, -, rfl⟩ := h
        exact ⟨b, rfl⟩
    have hβα : β < Order.succ β := Order.lt_succ β
    have hβω : β < ω₁ := hβα.trans hα
    obtain ⟨ih1, ih2⟩ := ih β hβα hβω
    constructor
    · intro k
      refine Set.Finite.subset ((ih1 k).union (Set.finite_singleton β)) ?_
      rintro ξ ⟨hξ, hk⟩
      rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hξ) with hξ' | hξ'
      · rw [E_succ, if_pos hξ'] at hk
        exact Or.inl ⟨hξ', hk⟩
      · exact Or.inr hξ'
    · intro δ hδ
      have hmem : ∀ ξ : Ordinal.{0}, ξ < δ → E (Order.succ β) ξ = E β ξ := by
        intro ξ hξ
        rw [E_succ, if_pos (lt_of_lt_of_le hξ (Order.lt_succ_iff.mp hδ))]
      rcases eq_or_lt_of_le (Order.lt_succ_iff.mp hδ) with heq | hδβ
      · subst heq
        have : {ξ : Ordinal.{0} | ξ < δ ∧ E (Order.succ δ) ξ ≠ E δ ξ} = ∅ := by
          ext ξ
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
          exact fun hξ => hmem ξ hξ
        rw [this]; exact Set.finite_empty
      · refine Set.Finite.subset (ih2 δ hδβ) ?_
        rintro ξ ⟨hξ, hne⟩
        exact ⟨hξ, fun h => hne ((hmem ξ hξ).trans h)⟩

