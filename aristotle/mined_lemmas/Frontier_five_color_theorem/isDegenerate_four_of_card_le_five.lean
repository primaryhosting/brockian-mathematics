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

theorem isDegenerate_four_of_card_le_five (hcard : Fintype.card V ≤ 5) : IsDegenerate G 4 := by
  intro s hs
  obtain ⟨v, hv⟩ := hs
  refine ⟨v, hv, ?_⟩
  calc ((s.erase v).filter (fun w => G.Adj v w)).card ≤ (s.erase v).card :=
        Finset.card_filter_le _ _
    _ = s.card - 1 := Finset.card_erase_of_mem hv
    _ ≤ Fintype.card V - 1 := by
        have := Finset.card_le_univ s
        omega
    _ ≤ 4 := by omega

/-- **The five colour theorem, special cases.**

Every planar graph that is `4`-degenerate, or has at most eleven vertices, or is triangle-free,
can be properly coloured with five colours.

Here planarity is the combinatorial notion `Frontier.IsHereditarilyPlanar`: every induced
subgraph carries a rotation system whose Euler characteristic is at least twice its number of
connected components, which is exactly what an embedding in the plane provides.

The hypothesis `hp` is not needed in the `4`-degenerate branch (where five colours are available
for a greedy colouring); it is what supplies, via Euler's formula, the degree bounds used in the
other two branches. The general case -- every planar graph is `5`-colourable -- requires the
Kempe chain argument and is not proved here. -/
