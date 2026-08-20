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

lemma norb_insert_two {π : Perm α} {D : Finset α} {c d : α} (hc : c ∉ D) (hd : d ∉ insert c D)
    (hfc : π c = c) (hfd : π d = d) :
    norb π (insert c (insert d D)) = norb π D + 2 := by
  have hdD : d ∉ D := fun hcon => hd (by simp [hcon])
  have hcd : c ≠ d := fun hcon => hd (by simp [hcon])
  have h2 : c ∉ insert d D := by simp [hcd, hc]
  rw [norb_insert_of_fixed h2 hfc, norb_insert_of_fixed hdD hfd]

/-- A dart of the old map is not in the cycle created by gluing two new fixed points. -/
