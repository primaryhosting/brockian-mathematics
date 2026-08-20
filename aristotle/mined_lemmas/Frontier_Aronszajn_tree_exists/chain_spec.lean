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

theorem chain_spec (hl : IsSuccLimit α) (hβ : β < α) (ih : ∀ γ < α, Good γ)
    (hf : f ∈ L β) (hq : SBd f β q) (n : ℕ) :
    chainF (prevOf α) α β f q n ∈ L (cseq α β n) ∧
      SBd (chainF (prevOf α) α β f q n) (cseq α β n) q := by
  induction n with
  | zero => exact ⟨hf, hq⟩
  | succ n ihn =>
      obtain ⟨h1, h2, -⟩ := chain_step hl hβ ih n ihn
      exact ⟨h1, h2⟩

