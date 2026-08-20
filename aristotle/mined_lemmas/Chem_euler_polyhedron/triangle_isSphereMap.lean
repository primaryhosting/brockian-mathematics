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

theorem triangle_isSphereMap :
    IsSphereMap ({0, 1, 2, 3, 4, 5} : Finset (Fin 6))
      (swap 1 4 * (swap 3 5 * swap 0 2)) (swap 4 5 * (swap 2 3 * swap 0 1)) := by
  have h0 : IsSphereMap ({0, 1} : Finset (Fin 6)) 1 (swap 0 1) := IsSphereMap.edge (by decide)
  have h1 := h0.pendant (x := 0) (c := 2) (d := 3) (by decide) (by decide) (by decide)
  simp only [Equiv.Perm.one_apply, mul_one] at h1
  have hface : ((swap (0 : Fin 6) 2) * (swap 2 3 * swap 0 1)).SameCycle
      ((swap (0 : Fin 6) 2) 1) ((swap (0 : Fin 6) 2) 3) := by decide
  have h2 := h1.chord (x := 1) (y := 3) (c := 4) (d := 5) (by decide) (by decide) (by decide)
    hface (by decide) (by decide)
  have e1 : (swap (0 : Fin 6) 2) 1 = 1 := by decide
  have e2 : (swap (0 : Fin 6) 2) 3 = 3 := by decide
  rw [e1, e2] at h2
  have hD : (insert 4 (insert 5 (insert 2 (insert 3 ({0, 1} : Finset (Fin 6)))))) =
      {0, 1, 2, 3, 4, 5} := by decide
  rw [hD] at h2
  exact h2

