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

noncomputable def Lstep (α : Ordinal.{0}) (P : Ordinal.{0} → Set Nd) : Set Nd :=
  if α = 0 then {fun _ => 0}
  else if IsSuccPrelimit α then
    {g | ∃ β, β < α ∧ ∃ f ∈ P β, ∃ q : ℚ, SBd f β q ∧ g = limExt P α β f q}
  else
    {g | ∃ f ∈ P (Ordinal.pred α), ∃ s : ℚ, (∀ γ < Ordinal.pred α, f γ < s) ∧
          g = snoc (Ordinal.pred α) f s}

/-- The `α`-th level of the tree. -/
