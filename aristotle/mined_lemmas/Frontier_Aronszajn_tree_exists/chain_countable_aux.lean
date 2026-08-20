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


theorem chain_countable_aux (C : Set Node) (hC : IsChain NodeLt C) : C.Countable := by
  by_contra hcount
  have hagree : ∀ x ∈ C, ∀ y ∈ C, ∀ ξ : Ordinal.{0}, ξ < x.lvl → ξ < y.lvl → x.fn ξ = y.fn ξ := by
    intro x hx y hy ξ hξx hξy
    rcases eq_or_ne x y with rfl | hne
    · rfl
    · rcases hC hx hy hne with h | h
      · exact h.2 ξ hξx
      · exact (h.2 ξ hξy).symm
  have hinj : Set.InjOn Node.lvl C := by
    intro x hx y hy hxy
    by_contra hne
    rcases hC hx hy hne with h | h
    · exact absurd hxy (ne_of_lt h.1)
    · exact absurd hxy.symm (ne_of_lt h.1)
  have hAunc : ¬ (Node.lvl '' C).Countable := fun h =>
    hcount (Set.countable_of_injective_of_countable_image hinj h)
  have habove : ∀ x ∈ C, ∃ y ∈ C, x.lvl < y.lvl := by
    intro x hx
    by_contra hcon
    push_neg at hcon
    refine hAunc (Set.Countable.mono ?_ (countable_Iio_iff.mpr (succ_lt_omega1 x.lvl_lt_omega1)))
    rintro β ⟨y, hy, rfl⟩
    exact Set.mem_Iio.mpr (Order.lt_succ_iff.mpr (hcon y hy))
  set D : Set Ordinal.{0} := {ξ | ∃ x ∈ C, ξ < x.lvl} with hD
  set F : Ordinal.{0} → ℕ :=
    fun ξ => if h : ∃ x, x ∈ C ∧ ξ < x.lvl then h.choose.fn ξ else 0 with hF
  have hFval : ∀ x ∈ C, ∀ ξ : Ordinal.{0}, ξ < x.lvl → F ξ = x.fn ξ := by
    intro x hx ξ hξ
    have hex : ∃ y, y ∈ C ∧ ξ < y.lvl := ⟨x, hx, hξ⟩
    rw [hF]
    simp only [dif_pos hex]
    exact hagree _ hex.choose_spec.1 x hx ξ hex.choose_spec.2 hξ
  have hDunc : ¬ D.Countable := by
    intro h
    refine hAunc (Set.Countable.mono ?_ h)
    rintro β ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := habove x hx
    exact ⟨y, hy, hxy⟩
  have hfin : ∀ (k : ℕ), ∀ ξ ∈ D, {η : Ordinal.{0} | (η ∈ D ∧ F η = k) ∧ η < ξ}.Finite := by
    intro k ξ hξ
    obtain ⟨x, hx, hξx⟩ := hξ
    refine Set.Finite.subset (x.finite_fibers k) ?_
    rintro η ⟨⟨-, hFη⟩, hηξ⟩
    have hηx : η < x.lvl := hηξ.trans hξx
    exact ⟨hηx, by rw [← hFval x hx η hηx]; exact hFη⟩
  have hScount : ∀ k : ℕ, {η : Ordinal.{0} | η ∈ D ∧ F η = k}.Countable := by
    intro k
    rw [Set.countable_iff_exists_injOn]
    refine ⟨fun η => {μ : Ordinal.{0} | (μ ∈ D ∧ F μ = k) ∧ μ < η}.ncard, ?_⟩
    have hmono : ∀ η ∈ {η : Ordinal.{0} | η ∈ D ∧ F η = k},
        ∀ η' ∈ {η : Ordinal.{0} | η ∈ D ∧ F η = k}, η < η' →
          {μ : Ordinal.{0} | (μ ∈ D ∧ F μ = k) ∧ μ < η}.ncard <
            {μ : Ordinal.{0} | (μ ∈ D ∧ F μ = k) ∧ μ < η'}.ncard := by
      intro η hη η' hη' hlt
      refine Set.ncard_lt_ncard ⟨fun μ hμ => ⟨hμ.1, hμ.2.trans hlt⟩, ?_⟩ (hfin k η' hη'.1)
      intro hsub
      exact absurd (hsub ⟨hη, hlt⟩).2 (lt_irrefl η)
    intro η hη η' hη' heq
    rcases lt_trichotomy η η' with h | h | h
    · exact absurd heq (ne_of_lt (hmono η hη η' hη' h))
    · exact h
    · exact absurd heq.symm (ne_of_lt (hmono η' hη' η hη h))
  refine hDunc (Set.Countable.mono ?_ (Set.countable_iUnion hScount))
  intro ξ hξ
  exact Set.mem_iUnion.mpr ⟨F ξ, hξ, rfl⟩

/-- **There exists an Aronszajn tree**: a tree of height `ω₁` all of whose levels are countable
and which has no uncountable chain. -/
