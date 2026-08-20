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

noncomputable def chainF (P : Ordinal.{0} → Set Nd) (α β : Ordinal.{0}) (f : Nd) (q : ℚ) :
    ℕ → Nd
  | 0 => f
  | n + 1 =>
      if h : ∃ g, g ∈ P (cseq α β (n+1)) ∧ (∀ γ < cseq α β n, g γ = chainF P α β f q n γ) ∧
          SBd g (cseq α β (n+1)) q then h.choose else fun _ => 0

/-- The node at a limit level obtained as the union of the chain. -/
