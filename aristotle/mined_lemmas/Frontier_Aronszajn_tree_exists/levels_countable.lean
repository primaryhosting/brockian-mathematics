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

theorem levels_countable (β : Ordinal.{0}) : {x : Node | nht x = β}.Countable := by
  rcases lt_or_ge β ω₁ with hβ | hβ
  · have hmaps : Set.MapsTo nfun {x : Node | nht x = β} (L β) := by
      intro x hx
      have : nht x = β := hx
      rw [← this]
      exact nfun_mem x
    have hinj : Set.InjOn nfun {x : Node | nht x = β} := by
      intro x hx y hy hxy
      have hx' : nht x = β := hx
      have hy' : nht y = β := hy
      refine node_ext (hx'.trans hy'.symm) ?_
      intro γ _
      rw [show nfun x = nfun y from hxy]
    exact hmaps.countable_of_injOn hinj (good β hβ).ctble
  · have : {x : Node | nht x = β} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact absurd (h ▸ nht_lt x) (not_lt.mpr hβ)
    rw [this]
    exact Set.countable_empty

/-- The tree property: the predecessors of a node of height `α` are indexed by the
ordinals below `α`. -/
