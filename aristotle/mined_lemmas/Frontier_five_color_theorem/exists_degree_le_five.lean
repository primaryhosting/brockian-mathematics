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

theorem exists_degree_le_five [Nonempty V] [DecidableRel G.Adj] (hp : IsPlanar G) :
    ∃ v : V, G.degree v ≤ 5 := by
  by_contra hcon
  push_neg at hcon
  have hdeg : ∀ v : V, 2 ≤ Nat.card (G.neighborSet v) := fun v => by
    rw [card_neighborSet_eq_degree']
    exact le_trans (by norm_num) (hcon v)
  have hbound := planar_edge_bound hp hdeg
  have hlow := mul_card_le_two_mul_card_edgeSet 6 (fun v => hcon v)
  have hpos : (0 : ℤ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  push_cast at hlow
  linarith

/-- **A nonempty planar graph on at most eleven vertices has a vertex of degree at most four.**
(The bound `11` is sharp: the icosahedron is a `5`-regular planar graph on twelve vertices.) -/
