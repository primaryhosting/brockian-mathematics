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

theorem card_dart_eq (G : SimpleGraph V) : Nat.card G.Dart = 2 * Nat.card G.edgeSet := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
    SimpleGraph.dart_card_eq_twice_card_edges]

omit [Fintype V] in
/-- If every vertex has a neighbour there are no isolated vertices. -/
