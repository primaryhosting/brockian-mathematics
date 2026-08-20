import Mathlib

/-!
# Construction of an Aronszajn tree

We build the classical (special) Aronszajn tree: nodes at level `α < ω₁` are strictly
increasing bounded functions `α → ℚ`, constructed by transfinite recursion so that each
level is countable and every node can be extended to any higher level while keeping a
prescribed rational bound.
-/

open Ordinal Cardinal Set Order
open scoped Classical

namespace Aronszajn

set_option autoImplicit false
set_option maxRecDepth 8000

/-- A node is (the total extension by `0` of) a function from a countable ordinal to `ℚ`. -/
abbrev Nd : Type 1 := Ordinal.{0} → ℚ

/-- `SBd f α q` says the values of `f` below `α` are bounded by some rational `< q`. -/

theorem good_succ {δ : Ordinal.{0}} (hd : Good δ) : Good (δ + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro g hg γ hγ
    rw [L_succ] at hg
    obtain ⟨f, hf, s, hs, rfl⟩ := hg
    have hδγ : δ < γ := succ_le_iff'.mp hγ
    rw [snoc, if_neg (not_lt.mpr hδγ.le), if_neg hδγ.ne']
  · rintro g hg γ ε hγε hε
    rw [L_succ] at hg
    obtain ⟨f, hf, s, hs, rfl⟩ := hg
    rcases lt_or_eq_of_le (lt_succ_iff'.mp hε) with h | rfl
    · rw [snoc_of_lt (hγε.trans h), snoc_of_lt h]
      exact hd.mono f hf γ ε hγε h
    · rw [snoc_of_lt hγε, snoc_self]
      exact hs γ hγε
  · rintro β hβ g hg
    rw [L_succ] at hg
    obtain ⟨f, hf, s, hs, rfl⟩ := hg
    have hβδ : β ≤ δ := lt_succ_iff'.mp hβ
    have htr : trunc β (snoc δ f s) = trunc β f := by
      funext γ
      rw [trunc, trunc]
      by_cases h : γ < β
      · rw [if_pos h, if_pos h, snoc_of_lt (lt_of_lt_of_le h hβδ)]
      · rw [if_neg h, if_neg h]
    rw [htr]
    rcases lt_or_eq_of_le hβδ with h | rfl
    · exact hd.coh β h f hf
    · rw [trunc_self (fun γ hγ => hd.zero_out f hf γ hγ)]
      exact hf
  · have hsub : L (δ + 1) ⊆ ⋃ f ∈ L δ, ⋃ s : ℚ, {snoc δ f s} := by
      intro g hg
      rw [L_succ] at hg
      obtain ⟨f, hf, s, -, rfl⟩ := hg
      exact Set.mem_biUnion hf (Set.mem_iUnion.mpr ⟨s, rfl⟩)
    exact Set.Countable.mono hsub
      (hd.ctble.biUnion (fun f _ => Set.countable_iUnion (fun s => Set.countable_singleton _)))
  · rintro β hβ f₀ hf₀ Q hQ
    have hβδ : β ≤ δ := lt_succ_iff'.mp hβ
    obtain ⟨f₁, hf₁, hag, hb⟩ : ∃ f₁ ∈ L δ, (∀ γ < β, f₁ γ = f₀ γ) ∧ SBd f₁ δ Q := by
      rcases lt_or_eq_of_le hβδ with h | rfl
      · exact hd.ext β h f₀ hf₀ Q hQ
      · exact ⟨f₀, hf₀, fun _ _ => rfl, hQ⟩
    obtain ⟨g, hg, hag', hb'⟩ := succ_ext f₁ hf₁ Q hb
    exact ⟨g, hg, fun γ hγ => (hag' γ (lt_of_lt_of_le hγ hβδ)).trans (hag γ hγ), hb'⟩

/-! ### Limit levels -/

section Limit

variable {α β : Ordinal.{0}} {f : Nd} {q : ℚ}

/-- Successor step of the chain construction at a limit level. -/
