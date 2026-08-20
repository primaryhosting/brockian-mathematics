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

theorem cseq_lt {α β : Ordinal.{0}} (hl : IsSuccLimit α) (hβ : β < α) (n : ℕ) :
    cseq α β n < α := by
  induction n with
  | zero => exact hβ
  | succ n ih =>
      have h1 : cseq α β (n+1) = max (cseq α β n + 1) (enumOrd' α n + 1) := rfl
      rw [h1]
      exact max_lt (hl.add_one_lt ih)
        (hl.add_one_lt (enumOrd'_lt (lt_of_le_of_lt (zero_le β) hβ) n))

