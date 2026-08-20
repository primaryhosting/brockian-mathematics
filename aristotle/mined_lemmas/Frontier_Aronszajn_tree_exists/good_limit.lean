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

theorem good_limit {α : Ordinal.{0}} (hl : IsSuccLimit α) (hc : (Set.Iio α).Countable)
    (ih : ∀ γ < α, Good γ) : Good α := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro g hg γ hγ
    rw [L_limit hl] at hg
    obtain ⟨β, hβ, f, hf, q, hq, rfl⟩ := hg
    exact limExt_zero_out hl hβ hγ
  · rintro g hg γ δ hγδ hδ
    rw [L_limit hl] at hg
    obtain ⟨β, hβ, f, hf, q, hq, rfl⟩ := hg
    exact limExt_mono hl hc hβ ih hf hq γ δ hγδ hδ
  · rintro β' hβ' g hg
    rw [L_limit hl] at hg
    obtain ⟨β, hβ, f, hf, q, hq, rfl⟩ := hg
    exact limExt_trunc hl hc hβ ih hf hq β' hβ'
  · have hsub : L α ⊆ ⋃ β ∈ Set.Iio α, ⋃ f ∈ L β, ⋃ q : ℚ, {limExt (prevOf α) α β f q} := by
      intro g hg
      rw [L_limit hl] at hg
      obtain ⟨β, hβ, f, hf, q, -, rfl⟩ := hg
      exact Set.mem_biUnion hβ (Set.mem_biUnion hf (Set.mem_iUnion.mpr ⟨q, rfl⟩))
    refine Set.Countable.mono hsub (hc.biUnion (fun β hβ => ?_))
    exact ((ih β hβ).ctble).biUnion
      (fun f _ => Set.countable_iUnion (fun q => Set.countable_singleton _))
  · rintro β hβ f hf Q ⟨r, hrQ, hr⟩
    refine ⟨limExt (prevOf α) α β f ((r + Q) / 2), ?_, ?_, ?_⟩
    · rw [L_limit hl]
      exact ⟨β, hβ, f, hf, (r + Q) / 2, ⟨r, by linarith, hr⟩, rfl⟩
    · exact limExt_agree hl hβ ih hf ⟨r, by linarith, hr⟩
    · refine ⟨(r + Q) / 2, by linarith, ?_⟩
      intro γ hγ
      exact le_of_lt (limExt_lt hl hc hβ ih hf ⟨r, by linarith, hr⟩ γ hγ)

