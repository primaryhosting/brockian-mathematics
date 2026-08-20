import Mathlib
namespace C2.CS2

/-- No boolean equals its own negation. -/

theorem no_universal_decider : ¬ ∃ b : Bool, b = !b := by
  rintro ⟨b, hb⟩
  cases b <;> simp at hb

/-- Cantor's diagonal argument: no map `α → (α → Bool)` is surjective. -/
