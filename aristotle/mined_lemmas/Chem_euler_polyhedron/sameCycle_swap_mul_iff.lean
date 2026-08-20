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

lemma sameCycle_swap_mul_iff {π : Perm α} {x y : α} (hxy : ¬ π.SameCycle x y) (z w : α) :
    (swap x y * π).SameCycle z w ↔ MergeRel π x y z w := by
  constructor
  · intro h
    obtain ⟨i, _, _, hi⟩ := h.exists_pow_eq _
    exact hi ▸ mergeRel_pow π x y z i
  · intro h
    rcases h with h | ⟨hz, hw⟩
    · by_cases hin : π.SameCycle z x ∨ π.SameCycle z y
      · have hw : π.SameCycle w x ∨ π.SameCycle w y := by
          rcases hin with hin | hin
          · exact Or.inl (h.symm.trans hin)
          · exact Or.inr (h.symm.trans hin)
        exact (sameCycle_swap_mul_of_mem hxy hin).symm.trans (sameCycle_swap_mul_of_mem hxy hw)
      · push_neg at hin
        obtain ⟨i, _, _, hi⟩ := h.exists_pow_eq _
        refine ⟨(i : ℤ), ?_⟩
        have := pow_swap_mul_apply_of_not_mem hin.1 hin.2 i
        simpa [this] using hi
    · exact (sameCycle_swap_mul_of_mem hxy hz).symm.trans (sameCycle_swap_mul_of_mem hxy hw)

/-! ### The orbit count changes by one -/

/-- Multiplying by a transposition whose two points lie in **different** cycles merges
those cycles: the number of orbits drops by one. -/
