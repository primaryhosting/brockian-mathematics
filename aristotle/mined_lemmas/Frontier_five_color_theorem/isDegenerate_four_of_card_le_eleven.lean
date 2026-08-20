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

theorem isDegenerate_four_of_card_le_eleven (h : IsHereditarilyPlanar G)
    (hcard : Fintype.card V ≤ 11) : IsDegenerate G 4 := by
  intro s hs
  obtain ⟨v₀, hv₀⟩ := hs
  have hne : Nonempty (↑s : Set V) := ⟨⟨v₀, hv₀⟩⟩
  haveI : DecidableRel (G.induce (↑s : Set V)).Adj := fun a b => ‹DecidableRel G.Adj› a.1 b.1
  have hcards : Fintype.card (↑s : Set V) ≤ 11 := by
    have h1 : Fintype.card (↑s : Set V) = s.card := Fintype.card_coe s
    have h2 : s.card ≤ Fintype.card V := Finset.card_le_univ s
    omega
  obtain ⟨v, hv⟩ :=
    exists_degree_le_four_of_card_le_eleven (G := G.induce (↑s : Set V)) (h s) hcards
  refine ⟨v.1, v.2, ?_⟩
  rw [← card_neighborSet_induce s v, Nat.card_eq_fintype_card,
    SimpleGraph.card_neighborSet_eq_degree]
  exact hv

/-- **The six colour theorem**: a (hereditarily) planar graph is `6`-colourable. -/
