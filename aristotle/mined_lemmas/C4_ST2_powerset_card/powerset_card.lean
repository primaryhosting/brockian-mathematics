import Mathlib
namespace C4.ST2

/-- The power set of a finite type of cardinality `n` has `2 ^ n` elements. -/

theorem powerset_card {α : Type*} [Fintype α] : Fintype.card (Set α) = 2 ^ Fintype.card α := by
  classical
  exact Fintype.card_set

/-- Cantor's theorem: no map `α → Set α` is surjective. -/
