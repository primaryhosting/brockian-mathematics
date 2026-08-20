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

theorem L_succ (δ : Ordinal.{0}) :
    L (δ + 1) = {g | ∃ f ∈ L δ, ∃ s : ℚ, (∀ γ < δ, f γ < s) ∧ g = snoc δ f s} := by
  have h0 : δ + 1 ≠ 0 := by
    rw [← Order.succ_eq_add_one]; exact Order.succ_ne_bot δ
  have hnp : ¬ IsSuccPrelimit (δ + 1) := by
    rw [← Order.succ_eq_add_one]; exact Order.not_isSuccPrelimit_succ δ
  have hpred : Ordinal.pred (δ + 1) = δ := by
    rw [← Order.succ_eq_add_one]; exact Ordinal.pred_succ δ
  rw [L_eq, Lstep, if_neg h0, if_neg hnp, hpred, prevOf_eq (by exact Order.lt_succ δ)]

