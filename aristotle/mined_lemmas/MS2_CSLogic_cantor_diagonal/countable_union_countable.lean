import Mathlib
namespace MS2.CSLogic

/-- Cantor's diagonal argument: no map `α → (α → Bool)` is surjective. -/

theorem countable_union_countable {α : Type*} (s : ℕ → Set α) (h : ∀ n, (s n).Countable) :
    (⋃ n, s n).Countable :=
  Set.countable_iUnion h

