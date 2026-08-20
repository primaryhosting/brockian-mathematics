import Mathlib
namespace C2.CS2

/-- No boolean equals its own negation. -/

theorem pigeon_functions {A B : Type*} [Fintype A] [Fintype B] (h : Fintype.card B < Fintype.card A)
    (f : A → B) : ∃ x y, x ≠ y ∧ f x = f y :=
  Fintype.exists_ne_map_eq_of_card_lt f h

end C2.CS2

