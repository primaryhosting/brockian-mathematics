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

theorem limExt_mono (hl : IsSuccLimit α) (hc : (Set.Iio α).Countable) (hβ : β < α)
    (ih : ∀ γ < α, Good γ) (hf : f ∈ L β) (hq : SBd f β q) :
    ∀ γ δ, γ < δ → δ < α → limExt (prevOf α) α β f q γ < limExt (prevOf α) α β f q δ := by
  intro γ δ hγδ hδ
  obtain ⟨n, hn⟩ := cseq_cofinal (β := β) hc hδ
  rw [limExt_eq hl hβ ih hf hq n (hγδ.trans hn), limExt_eq hl hβ ih hf hq n hn]
  exact (ih _ (cseq_lt hl hβ n)).mono _ (chain_spec hl hβ ih hf hq n).1 γ δ hγδ hn

