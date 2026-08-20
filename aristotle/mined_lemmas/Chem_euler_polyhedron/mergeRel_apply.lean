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

lemma mergeRel_apply (π : Perm α) (x y z : α) : MergeRel π x y z ((swap x y * π) z) := by
  have hstep : π.SameCycle z (π z) := ⟨1, by simp⟩
  by_cases h1 : π z = x
  · have : (swap x y * π) z = y := by simp [Perm.mul_apply, h1]
    rw [this]
    exact Or.inr ⟨Or.inl (h1 ▸ hstep), Or.inr (SameCycle.refl _ _)⟩
  · by_cases h2 : π z = y
    · have : (swap x y * π) z = x := by simp [Perm.mul_apply, h2]
      rw [this]
      exact Or.inr ⟨Or.inr (h2 ▸ hstep), Or.inl (SameCycle.refl _ _)⟩
    · have : (swap x y * π) z = π z := by
        simp [Perm.mul_apply, swap_apply_of_ne_of_ne h1 h2]
      rw [this]
      exact Or.inl hstep

omit [Fintype α] in
