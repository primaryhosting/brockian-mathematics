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

theorem L_eq (α : Ordinal.{0}) : L α = Lstep α (prevOf α) := by
  have hfun : (fun b => if h : b < α then L b else (∅ : Set Nd)) = prevOf α := by
    funext b
    rw [prevOf]
    by_cases h : b < α
    · rw [dif_pos h, if_pos h]
    · rw [dif_neg h, if_neg h]
  conv_lhs => rw [L, Ordinal.lt_wf.fix_eq]
  rw [← hfun]
  rfl

