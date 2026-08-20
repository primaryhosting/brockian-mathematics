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

lemma norb_pair_swap {a b : α} (hab : a ≠ b) : norb (swap a b) {a, b} = 1 := by
  have hsame : (swap a b).SameCycle a b := ⟨1, by simp⟩
  have h : ∀ z ∈ ({a, b} : Finset α), cyc (swap a b) {a, b} z = {a, b} := by
    intro z hz
    have : cyc (swap a b) {a, b} a = {a, b} := by
      ext w
      simp only [mem_cyc, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hw, -⟩; exact hw
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, SameCycle.refl _ _⟩
        · exact ⟨Or.inr rfl, hsame⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact this
    · rw [Finset.mem_singleton] at hz
      subst hz
      rw [← cyc_eq_of_sameCycle hsame]
      exact this
  unfold norb
  rw [Finset.image_congr (g := fun _ => ({a, b} : Finset α)) (fun z hz => h z hz),
    Finset.image_const ⟨a, by simp⟩]
  simp

/-- **Euler's polyhedron formula**: for a map drawn on the sphere (the combinatorial
description of the surface of a convex polyhedron), `V - E + F = 2`. -/
