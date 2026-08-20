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

theorem chain_agree (hl : IsSuccLimit α) (hβ : β < α) (ih : ∀ γ < α, Good γ)
    (hf : f ∈ L β) (hq : SBd f β q) (n : ℕ) :
    ∀ γ < cseq α β n, chainF (prevOf α) α β f q (n + 1) γ = chainF (prevOf α) α β f q n γ :=
  (chain_step hl hβ ih n (chain_spec hl hβ ih hf hq n)).2.2

