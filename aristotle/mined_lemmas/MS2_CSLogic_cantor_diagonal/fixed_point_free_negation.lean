import Mathlib
namespace MS2.CSLogic

/-- Cantor's diagonal argument: no map `α → (α → Bool)` is surjective. -/

theorem fixed_point_free_negation : ¬ ∃ b : Bool, b = !b := by
  rintro ⟨b, hb⟩
  cases b <;> simp at hb

