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

theorem five_color_theorem_of_card_le_five (hp : IsHereditarilyPlanar G)
    (hcard : Fintype.card V ≤ 5) : G.Colorable 5 :=
  five_color_theorem hp (Or.inl (isDegenerate_four_of_card_le_five hcard))

/-- **Every planar graph on at most eleven vertices is `5`-colourable.** Euler's formula forces
such a graph, and each of its induced subgraphs, to have a vertex of degree at most four, so no
Kempe chain argument is needed. The bound `11` is sharp for this argument: the icosahedron is a
`5`-regular planar graph on twelve vertices. -/
