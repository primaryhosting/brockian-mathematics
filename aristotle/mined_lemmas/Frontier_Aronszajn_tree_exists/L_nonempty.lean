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

theorem L_nonempty {β : Ordinal.{0}} (hβ : β < ω₁) : (L β).Nonempty := by
  rcases eq_or_ne β 0 with rfl | h0
  · exact ⟨fun _ => 0, by rw [L_zero]; rfl⟩
  · have hpos : (0 : Ordinal.{0}) < β := pos_iff_ne_zero.mpr h0
    obtain ⟨g, hg, -, -⟩ :=
      (good β hβ).ext 0 hpos (fun _ => 0) (by rw [L_zero]; rfl) 1 ⟨0, by norm_num, by simp⟩
    exact ⟨g, hg⟩

