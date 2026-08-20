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

lemma sameCycle_swap_mul_of_mem {π : Perm α} {x y z : α} (hxy : ¬ π.SameCycle x y)
    (hz : π.SameCycle z x ∨ π.SameCycle z y) : (swap x y * π).SameCycle x z := by
  rcases hz with hz | hz
  · exact sameCycle_swap_mul_of_left hxy hz.symm
  · exact (sameCycle_swap_mul_xy hxy).trans (sameCycle_swap_mul_of_right hxy hz.symm)

/-- The relation describing the cycles of `swap x y * π`: the `π`-cycles, with those of
`x` and `y` glued together. -/
