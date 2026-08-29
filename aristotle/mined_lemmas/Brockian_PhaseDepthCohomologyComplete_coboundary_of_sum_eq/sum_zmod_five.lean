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
