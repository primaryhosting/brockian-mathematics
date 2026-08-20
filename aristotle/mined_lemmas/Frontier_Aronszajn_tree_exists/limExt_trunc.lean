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

theorem limExt_trunc (hl : IsSuccLimit α) (hc : (Set.Iio α).Countable) (hβ : β < α)
    (ih : ∀ γ < α, Good γ) (hf : f ∈ L β) (hq : SBd f β q) :
    ∀ β' < α, trunc β' (limExt (prevOf α) α β f q) ∈ L β' := by
  intro β' hβ'
  obtain ⟨n, hn⟩ := cseq_cofinal (β := β) hc hβ'
  have heq : trunc β' (limExt (prevOf α) α β f q) = trunc β' (chainF (prevOf α) α β f q n) := by
    funext γ
    rw [trunc, trunc]
    by_cases hγ : γ < β'
    · rw [if_pos hγ, if_pos hγ, limExt_eq hl hβ ih hf hq n (hγ.trans hn)]
    · rw [if_neg hγ, if_neg hγ]
  rw [heq]
  exact (ih _ (cseq_lt hl hβ n)).coh β' hn _ (chain_spec hl hβ ih hf hq n).1

end Limit

