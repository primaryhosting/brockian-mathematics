import Mathlib

/-!
# Orbits of a permutation

Minimal theory of orbits of a permutation of a finite type, as needed for face counting in a
combinatorial embedding of a graph: a permutation all of whose orbits have at least `n` elements
has at most `#α / n` orbits.
-/

namespace Frontier

variable {α : Type*}

/-- The setoid on `α` whose equivalence classes are the orbits of the permutation `f`. -/

theorem five_color_theorem_of_card_le_eleven (hp : IsHereditarilyPlanar G)
    (hcard : Fintype.card V ≤ 11) : G.Colorable 5 :=
  five_color_theorem hp (Or.inr (Or.inl hcard))

end Frontier

