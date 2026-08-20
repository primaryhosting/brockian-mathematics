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

theorem six_color_theorem (h : IsHereditarilyPlanar G) : G.Colorable 6 :=
  colorable_of_isDegenerate 5 (isDegenerate_of_isHereditarilyPlanar h)

omit [Fintype V] in
/-- A triangle-free hereditarily planar graph is `3`-degenerate. -/
