/-
# Coboundary Of Sum Eq
Category: B Brockian Frontier
Target: Brockian.PhaseDepthCohomologyComplete.coboundary_of_sum_eq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Coboundary Of Sum Eq
Category: B Brockian Frontier
Target: Brockian.PhaseDepthCohomologyComplete.coboundary_of_sum_eq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian
namespace PhaseDepthCohomologyComplete

/-- Expansion of a sum over `ZMod 5` as the sum of its five values. -/
private lemma sum_zmod_five {G : Type*} [AddCommGroup G] (c : ZMod 5 → G) :
    Finset.univ.sum c = c 0 + c 1 + c 2 + c 3 + c 4 := by
  have h : Finset.univ.sum c = ∑ i : Fin 5, c (i : ZMod 5) := rfl
  rw [h, Fin.sum_univ_five]

/-- **Completeness of the discrete coboundary criterion on the 5-cycle.**
If two cochains `c1, c2 : ZMod 5 → G` have equal total sum, then their difference is a
coboundary: there is `h : ZMod 5 → G` with `c1 j - c2 j = h (j + 1) - h j` for all `j`. -/
theorem coboundary_of_sum_eq {G : Type*} [AddCommGroup G] (c1 c2 : ZMod 5 → G)
    (hs : (Finset.univ.sum c1) = (Finset.univ.sum c2)) :
    ∃ h : ZMod 5 → G, ∀ j, c1 j - c2 j = h (j + 1) - h j := by
  rw [sum_zmod_five, sum_zmod_five] at hs
  have hsum : (c1 0 - c2 0) + (c1 1 - c2 1) + (c1 2 - c2 2) + (c1 3 - c2 3) + (c1 4 - c2 4) = 0 :=
    by linear_combination (norm := abel) hs
  set g : ZMod 5 → G := fun j => c1 j - c2 j with hg
  refine ⟨fun k => if k = 0 then 0 else if k = 1 then g 0 else if k = 2 then g 0 + g 1
      else if k = 3 then g 0 + g 1 + g 2 else g 0 + g 1 + g 2 + g 3, ?_⟩
  have hcases : ∀ j : ZMod 5, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by decide
  intro j
  rcases hcases j with rfl|rfl|rfl|rfl|rfl <;>
    simp only [show ((0:ZMod 5)+1) = 1 from rfl, show ((1:ZMod 5)+1) = 2 from rfl,
      show ((2:ZMod 5)+1) = 3 from rfl, show ((3:ZMod 5)+1) = 4 from rfl,
      show ((4:ZMod 5)+1) = 0 from rfl] <;>
    norm_num +decide [hg]
  -- only the seam case `j = 4` (where `j + 1 = 0`) remains; it closes by zero total sum
  linear_combination (norm := abel) hsum

end PhaseDepthCohomologyComplete
end Brockian

#print axioms Brockian.PhaseDepthCohomologyComplete.coboundary_of_sum_eq

