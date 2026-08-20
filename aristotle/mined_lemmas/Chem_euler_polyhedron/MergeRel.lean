import RequestProject.EulerPolyhedron

/-!
# Fullerene cages have exactly twelve pentagonal faces

A fullerene cage is a polyhedral (spherical) carbon cage in which every atom has exactly three
neighbours and every ring is a pentagon or a hexagon.  Combining Euler's formula
`V - E + F = 2` with the two incidence counts `3V = 2E` and `5p + 6h = 2E` forces the number
of pentagons to be exactly `12`, no matter how many hexagons there are.
-/

namespace Chem

open Equiv Equiv.Perm Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ### The edge involution -/

omit [Fintype α] in
/-- The edge permutation of a sphere map is an involution. -/

lemma MergeRel.trans {π : Perm α} {x y z w u : α} (h1 : MergeRel π x y z w)
    (h2 : MergeRel π x y w u) : MergeRel π x y z u := by
  rcases h1 with h1 | ⟨hz, hw⟩
  · rcases h2 with h2 | ⟨hw, hu⟩
    · exact Or.inl (h1.trans h2)
    · refine Or.inr ⟨?_, hu⟩
      rcases hw with hw | hw
      · exact Or.inl (h1.trans hw)
      · exact Or.inr (h1.trans hw)
  · rcases h2 with h2 | ⟨_, hu⟩
    · refine Or.inr ⟨hz, ?_⟩
      rcases hw with hw | hw
      · exact Or.inl (h2.symm.trans hw)
      · exact Or.inr (h2.symm.trans hw)
    · exact Or.inr ⟨hz, hu⟩

omit [Fintype α] in
