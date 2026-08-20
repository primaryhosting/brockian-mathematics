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

theorem good (α : Ordinal.{0}) (hα : α < ω₁) : Good α := by
  induction α using Ordinal.lt_wf.induction with
  | _ α ih =>
    rcases eq_or_ne α 0 with rfl | h0
    · exact good_zero
    · by_cases hl : IsSuccPrelimit α
      · have hl' : IsSuccLimit α :=
          ⟨by rw [isMin_iff_eq_bot, Ordinal.bot_eq_zero]; exact h0, hl⟩
        exact good_limit hl' (Iio_countable hα) (fun γ hγ => ih γ hγ (hγ.trans hα))
      · have hp : Ordinal.pred α + 1 = α := by
          rw [← Order.succ_eq_add_one]
          exact Ordinal.succ_pred_eq_iff_not_isSuccPrelimit.mpr hl
        have hlt : Ordinal.pred α < α := Ordinal.pred_lt_iff_not_isSuccPrelimit.mpr hl
        have := good_succ (ih (Ordinal.pred α) hlt (hlt.trans hα))
        rwa [hp] at this

end Aronszajn

import RequestProject.Aronszajn

/-!
# The Aronszajn tree

From the levels `L α` constructed in `RequestProject.Aronszajn` we assemble the tree of
nodes and verify the defining properties of an Aronszajn tree.
-/

open Ordinal Cardinal Set Order
open scoped Classical

namespace Aronszajn

set_option autoImplicit false
set_option maxRecDepth 8000

/-- A node of the tree: a level `α < ω₁` together with an element of `L α`. -/
