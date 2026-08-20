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

lemma card_eq_mul_norb {π : Perm α} {D : Finset α} {k : ℕ} (h : ∀ z ∈ D, (cyc π D z).card = k) :
    D.card = k * norb π D := by
  classical
  rw [card_eq_sum_card_cyc π D]
  have hk : ∀ C ∈ D.image (cyc π D), C.card = k := by
    intro C hC
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hC
    exact h z hz
  rw [Finset.sum_congr rfl hk]
  simp [norb, mul_comm]

end Chem

import RequestProject.EulerPolyhedron

/-!
# A worked example

A small sanity check that `Chem.IsSphereMap` really describes maps on the sphere: we build the
triangle (a cycle of length three, drawn on the sphere) out of the constructors and check that
its vertex, edge and face counts are `3`, `3` and `2`, so that `V - E + F = 3 - 3 + 2 = 2`.

The six darts are `0, …, 5 : Fin 6`; the construction is: start with the edge `{0,1}`, attach a
pendant edge `{2,3}` at the dart `0`, and finally close the triangle with a chord `{4,5}`
joining the two corners following the darts `1` and `3`.
-/

namespace Chem

open Equiv Equiv.Perm Finset

/-- The triangle is a map on the sphere. -/
