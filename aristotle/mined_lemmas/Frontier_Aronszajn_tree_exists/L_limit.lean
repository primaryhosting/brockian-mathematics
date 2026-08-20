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

theorem L_limit {α : Ordinal.{0}} (hl : IsSuccLimit α) :
    L α = {g | ∃ β, β < α ∧ ∃ f ∈ L β, ∃ q : ℚ, SBd f β q ∧ g = limExt (prevOf α) α β f q} := by
  have h0 : α ≠ 0 := by
    rintro rfl
    exact hl.not_isMin isMin_bot
  rw [L_eq, Lstep, if_neg h0, if_pos hl.isSuccPrelimit]
  ext g
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨β, hβ, f, hf, q, hq, rfl⟩
    exact ⟨β, hβ, f, by rwa [prevOf_eq hβ] at hf, q, hq, rfl⟩
  · rintro ⟨β, hβ, f, hf, q, hq, rfl⟩
    exact ⟨β, hβ, f, by rwa [prevOf_eq hβ], q, hq, rfl⟩

/-! ### The invariants -/

/-- The invariants maintained by the transfinite construction of the levels. -/
structure Good (α : Ordinal.{0}) : Prop where
  zero_out : ∀ f ∈ L α, ∀ γ, α ≤ γ → f γ = 0
  mono : ∀ f ∈ L α, ∀ γ δ, γ < δ → δ < α → f γ < f δ
  coh : ∀ β < α, ∀ f ∈ L α, trunc β f ∈ L β
  ctble : (L α).Countable
  ext : ∀ β < α, ∀ f ∈ L β, ∀ q : ℚ, SBd f β q → ∃ g ∈ L α, (∀ γ < β, g γ = f γ) ∧ SBd g α q

