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

theorem isDegenerate_of_isHereditarilyPlanar (h : IsHereditarilyPlanar G) :
    IsDegenerate G 5 := by
  classical
  intro s hs
  obtain ⟨v₀, hv₀⟩ := hs
  have hne : Nonempty (↑s : Set V) := ⟨⟨v₀, hv₀⟩⟩
  haveI : DecidableRel (G.induce (↑s : Set V)).Adj := fun a b => ‹DecidableRel G.Adj› a.1 b.1
  obtain ⟨v, hv⟩ := exists_degree_le_five (G := G.induce (↑s : Set V)) (h s)
  refine ⟨v.1, v.2, ?_⟩
  rw [← card_neighborSet_induce s v, Nat.card_eq_fintype_card,
    SimpleGraph.card_neighborSet_eq_degree]
  exact hv

omit [Fintype V] [DecidableEq V] in
/-- Non-vacuity check: an edgeless graph is hereditarily planar. -/
