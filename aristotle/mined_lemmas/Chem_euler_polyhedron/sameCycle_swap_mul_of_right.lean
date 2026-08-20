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

lemma sameCycle_swap_mul_of_right {π : Perm α} {x y z : α} (hxy : ¬ π.SameCycle x y)
    (h : π.SameCycle y z) : (swap x y * π).SameCycle y z := by
  have h' := sameCycle_swap_mul_of_left (x := y) (y := x) (fun hc => hxy hc.symm) h
  rwa [swap_comm] at h'

/-- Anything in the cycle of `x` or of `y` lands in the merged cycle. -/
