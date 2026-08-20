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

lemma not_sameCycle_swap_mul_fixed' {π : Perm α} {u c d : α} (hfc : π c = c) (hfd : π d = d)
    (hcd : c ≠ d) (huc : u ≠ c) (hud : u ≠ d) : ¬ (swap c d * π).SameCycle u d := by
  have h := not_sameCycle_swap_mul_fixed (c := d) (d := c) hfd hfc hcd.symm hud huc
  rwa [swap_comm] at h

