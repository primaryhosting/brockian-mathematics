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

theorem limExt_eq (hl : IsSuccLimit α) (hβ : β < α) (ih : ∀ γ < α, Good γ)
    (hf : f ∈ L β) (hq : SBd f β q) (n : ℕ) {γ : Ordinal.{0}} (hγ : γ < cseq α β n) :
    limExt (prevOf α) α β f q γ = chainF (prevOf α) α β f q n γ := by
  have hne : ∃ k, γ < cseq α β k := ⟨n, hγ⟩
  have hm : γ < cseq α β (sInf {k | γ < cseq α β k}) := Nat.sInf_mem hne
  have hmn : sInf {k | γ < cseq α β k} ≤ n := Nat.sInf_le hγ
  rw [limExt, if_pos hne]
  exact (chain_agree' hl hβ ih hf hq hmn γ hm).symm

