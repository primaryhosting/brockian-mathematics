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

theorem enumOrd'_surj {α : Ordinal.{0}} (hc : (Set.Iio α).Countable) {β : Ordinal.{0}}
    (hβ : β < α) : ∃ n, enumOrd' α n = β := by
  have h : ∃ e : ℕ → Ordinal.{0}, ∀ β < α, ∃ m, e m = β := by
    rcases Set.countable_iff_exists_subset_range.mp hc with ⟨e, he⟩
    exact ⟨e, fun b hb => he hb⟩
  obtain ⟨m, hm⟩ := h.choose_spec β hβ
  refine ⟨m, ?_⟩
  unfold enumOrd'
  rw [dif_pos h, if_pos (by rw [hm]; exact hβ), hm]

/-- An increasing sequence starting at `β` and cofinal in `α`. -/
