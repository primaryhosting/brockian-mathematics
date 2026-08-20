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

theorem good_zero : Good 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f hf γ _
    rw [L_zero] at hf
    rw [hf]
  · intro f _ γ δ _ hδ
    exact absurd hδ (by simp)
  · intro β hβ
    exact absurd hβ (by simp)
  · rw [L_zero]; exact Set.countable_singleton _
  · intro β hβ
    exact absurd hβ (by simp)

/-! ### Successor levels -/

