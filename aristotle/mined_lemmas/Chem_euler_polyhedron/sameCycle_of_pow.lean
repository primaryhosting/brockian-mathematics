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

lemma sameCycle_of_pow {π : Perm α} {x : α} (i : ℕ) : π.SameCycle x ((π ^ i) x) :=
  ⟨(i : ℤ), by simp⟩

/-! ### Cycles of `swap x y * π` when `x` and `y` are in different cycles -/

/-- If `x` and `y` are in different `π`-cycles, then every element of the `π`-cycle of `x`
is in the `(swap x y * π)`-cycle of `x`. -/
