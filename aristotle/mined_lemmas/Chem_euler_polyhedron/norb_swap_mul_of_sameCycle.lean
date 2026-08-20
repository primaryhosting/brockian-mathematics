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

theorem norb_swap_mul_of_sameCycle {π : Perm α} {D : Finset α} {x y : α}
    (hx : x ∈ D) (hy : y ∈ D) (hne : x ≠ y) (h : π.SameCycle x y) :
    norb (swap x y * π) D = norb π D + 1 := by
  have hns := not_sameCycle_swap_mul_of_sameCycle hne h
  have key := norb_swap_mul_of_not_sameCycle (π := swap x y * π) hx hy hns
  rw [← mul_assoc, swap_mul_self, one_mul] at key
  omega

/-! ### Adding a new fixed point -/

omit [DecidableEq α] [Fintype α] in
