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

lemma card_eq_sum_card_cyc (π : Perm α) (D : Finset α) :
    D.card = ∑ C ∈ D.image (cyc π D), C.card := by
  classical
  rw [Finset.card_eq_sum_card_image (cyc π D) D]
  refine Finset.sum_congr rfl ?_
  intro C hC
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hC
  congr 1
  ext z
  simp only [Finset.mem_filter, mem_cyc]
  constructor
  · rintro ⟨hzD, hzc⟩
    exact ⟨hzD, ((cyc_eq_iff hw).1 hzc).symm⟩
  · rintro ⟨hzD, hsc⟩
    exact ⟨hzD, (cyc_eq_iff hw).2 hsc.symm⟩

/-- If every orbit meeting `D` has `k` elements, then `|D| = k * (number of orbits)`. -/
