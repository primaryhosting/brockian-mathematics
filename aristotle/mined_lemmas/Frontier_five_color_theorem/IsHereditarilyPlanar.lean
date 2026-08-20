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

def IsHereditarilyPlanar (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, IsPlanar (G.induce (↑s : Set V))

omit [Fintype V] in
/-- The number of neighbours of `v` inside `s` computed in the induced subgraph. -/
