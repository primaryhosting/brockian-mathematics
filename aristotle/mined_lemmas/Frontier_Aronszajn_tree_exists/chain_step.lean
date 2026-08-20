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

theorem chain_step (hl : IsSuccLimit α) (hβ : β < α) (ih : ∀ γ < α, Good γ) (n : ℕ)
    (hn : chainF (prevOf α) α β f q n ∈ L (cseq α β n) ∧
      SBd (chainF (prevOf α) α β f q n) (cseq α β n) q) :
    chainF (prevOf α) α β f q (n + 1) ∈ L (cseq α β (n + 1)) ∧
      SBd (chainF (prevOf α) α β f q (n + 1)) (cseq α β (n + 1)) q ∧
      ∀ γ < cseq α β n, chainF (prevOf α) α β f q (n + 1) γ = chainF (prevOf α) α β f q n γ := by
  have h1 : cseq α β (n + 1) < α := cseq_lt hl hβ (n + 1)
  have hex : ∃ g, g ∈ prevOf α (cseq α β (n + 1)) ∧
      (∀ γ < cseq α β n, g γ = chainF (prevOf α) α β f q n γ) ∧
      SBd g (cseq α β (n + 1)) q := by
    obtain ⟨g, hg, ha, hb⟩ := (ih _ h1).ext (cseq α β n) (cseq_lt_succ α β n)
      (chainF (prevOf α) α β f q n) hn.1 q hn.2
    exact ⟨g, by rwa [prevOf_eq h1], ha, hb⟩
  have heq : chainF (prevOf α) α β f q (n + 1) = hex.choose := by
    rw [chainF, dif_pos hex]
  have hmem : ∀ g : Nd, g ∈ prevOf α (cseq α β (n + 1)) → g ∈ L (cseq α β (n + 1)) := by
    intro g hg
    rwa [prevOf_eq h1] at hg
  obtain ⟨hm, ha, hb⟩ := hex.choose_spec
  exact ⟨heq ▸ hmem _ hm, heq ▸ hb, fun γ hγ => by rw [heq]; exact ha γ hγ⟩

