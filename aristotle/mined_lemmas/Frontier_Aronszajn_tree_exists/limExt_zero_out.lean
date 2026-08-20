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

theorem limExt_zero_out (hl : IsSuccLimit α) (hβ : β < α) {γ : Ordinal.{0}} (hγ : α ≤ γ) :
    limExt (prevOf α) α β f q γ = 0 := by
  have hne : ¬ ∃ k, γ < cseq α β k := by
    rintro ⟨k, hk⟩
    exact absurd (hk.trans (cseq_lt hl hβ k)) (not_lt.mpr hγ)
  rw [limExt, if_neg hne]

