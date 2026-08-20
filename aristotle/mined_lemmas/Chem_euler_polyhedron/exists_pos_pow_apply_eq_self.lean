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

lemma exists_pos_pow_apply_eq_self (π : Perm α) (x : α) : ∃ n, 0 < n ∧ (π ^ n) x = x := by
  refine ⟨orderOf π, orderOf_pos π, ?_⟩
  rw [pow_orderOf_eq_one]
  rfl

omit [DecidableEq α] [Fintype α] in
