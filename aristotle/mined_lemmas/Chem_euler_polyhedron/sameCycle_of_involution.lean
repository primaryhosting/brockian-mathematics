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

lemma sameCycle_of_involution {e : Perm α} (h2 : e * e = 1) {z w : α} (h : e.SameCycle z w) :
    w = z ∨ w = e z := by
  obtain ⟨i, hi⟩ := h
  have hsq : e ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h2
  rcases Int.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    have : e ^ i = 1 := by
      rw [hk, show k + k = 2 * k by ring, zpow_mul, hsq, one_zpow]
    rw [← hi, this]
    rfl
  · right
    have : e ^ i = e := by
      rw [hk, zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]
    rw [← hi, this]

/-- The edge (orbit of the edge involution) through a dart consists of exactly its two darts. -/
