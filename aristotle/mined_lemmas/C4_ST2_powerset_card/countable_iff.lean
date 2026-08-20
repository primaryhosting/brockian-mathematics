import Mathlib
namespace C4.ST2

/-- The power set of a finite type of cardinality `n` has `2 ^ n` elements. -/

theorem countable_iff {α : Type*} :
    (Set.univ : Set α).Countable ↔ Nonempty (α ↪ ℕ) := by
  rw [Set.countable_univ_iff, countable_iff_nonempty_embedding]

end C4.ST2

