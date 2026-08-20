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

theorem trunc_self {β : Ordinal.{0}} {f : Nd} (h : ∀ γ, β ≤ γ → f γ = 0) : trunc β f = f := by
  funext γ
  rw [trunc]
  by_cases hγ : γ < β
  · rw [if_pos hγ]
  · rw [if_neg hγ, h γ (not_lt.mp hγ)]

