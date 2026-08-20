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

lemma not_sameCycle_of_fixed {π : Perm α} {u v : α} (hfix : π v = v) (hne : u ≠ v) :
    ¬ π.SameCycle u v := fun h => hne (sameCycle_fixed hfix h.symm)

omit [Fintype α] in
/-- Structural invariants: both permutations fix every dart outside `D` and preserve `D`. -/
