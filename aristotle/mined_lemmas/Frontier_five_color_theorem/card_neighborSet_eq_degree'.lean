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

theorem card_neighborSet_eq_degree' [DecidableRel G.Adj] (v : V) :
    Nat.card (G.neighborSet v) = G.degree v := by
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]

/-- **Every nonempty planar graph has a vertex of degree at most five.** -/
