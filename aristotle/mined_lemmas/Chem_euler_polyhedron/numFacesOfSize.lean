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

noncomputable def numFacesOfSize (D : Finset α) (s e : Perm α) (k : ℕ) : ℕ :=
  ((D.image (cyc (s * e) D)).filter (fun C => C.card = k)).card

/-- **A fullerene cage has exactly twelve pentagonal faces.**

For a map on the sphere in which every vertex has degree three and every face is a pentagon
or a hexagon, the number of pentagonal faces is exactly `12` (whatever the number of
hexagons is). -/
