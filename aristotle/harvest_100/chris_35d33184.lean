/-
# Coboundary Of Sum Eq
Category: B Brockian Frontier
Target: Brockian.PhaseDepthCohomologyComplete.coboundary_of_sum_eq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.PhaseDepthCohomologyComplete

/-- Completeness half of the discrete-cohomology no-go on the 5-cycle: if two cochains
`c1 c2 : ZMod 5 → G` have the same total sum, then their difference is a coboundary,
i.e. there is `h : ZMod 5 → G` with `c1 j - c2 j = h (j + 1) - h j` for all `j`.
The witness is the partial-sum function of `g j = c1 j - c2 j`; the seam at `j = 4`
closes precisely because the total sum of `g` vanishes. -/
theorem coboundary_of_sum_eq {G : Type*} [AddCommGroup G] (c1 c2 : ZMod 5 → G)
    (hs : (Finset.univ.sum c1) = (Finset.univ.sum c2)) :
    ∃ h : ZMod 5 → G, ∀ j, c1 j - c2 j = h (j + 1) - h j := by
  set g : ZMod 5 → G := fun j => c1 j - c2 j with hg
  have hsum : g 0 + g 1 + g 2 + g 3 + g 4 = 0 := by
    have h1 : (Finset.univ.sum g) = 0 := by
      simp only [hg, Finset.sum_sub_distrib, hs, sub_self]
    rwa [show (Finset.univ.sum g) = g 0 + g 1 + g 2 + g 3 + g 4 from by
      show ∑ i : Fin 5, g i = _
      rw [Fin.sum_univ_five]] at h1
  refine ⟨fun j => ∑ i ∈ Finset.range (ZMod.val j), g (i : ZMod 5), ?_⟩
  intro j
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by revert j; decide
  rcases hj with rfl | rfl | rfl | rfl | rfl <;> show g _ = _ <;> simp only []
  · rw [show ZMod.val ((0 : ZMod 5) + 1) = 1 from by decide,
      show ZMod.val (0 : ZMod 5) = 0 from by decide]
    simp
  · rw [show ZMod.val ((1 : ZMod 5) + 1) = 2 from by decide,
      show ZMod.val (1 : ZMod 5) = 1 from by decide]
    simp [Finset.sum_range_succ]
  · rw [show ZMod.val ((2 : ZMod 5) + 1) = 3 from by decide,
      show ZMod.val (2 : ZMod 5) = 2 from by decide]
    simp [Finset.sum_range_succ]
  · rw [show ZMod.val ((3 : ZMod 5) + 1) = 4 from by decide,
      show ZMod.val (3 : ZMod 5) = 3 from by decide]
    simp [Finset.sum_range_succ]
  · rw [show ZMod.val ((4 : ZMod 5) + 1) = 0 from by decide,
      show ZMod.val (4 : ZMod 5) = 4 from by decide]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, zero_add, zero_sub]
    linear_combination (norm := abel) hsum

end Brockian.PhaseDepthCohomologyComplete

#print axioms Brockian.PhaseDepthCohomologyComplete.coboundary_of_sum_eq

