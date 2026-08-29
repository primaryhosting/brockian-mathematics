import Mathlib

/-!
# Coboundary Of Sum Eq
Category: B Brockian Frontier
Target: Brockian.PhaseDepthCohomologyComplete.coboundary_of_sum_eq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PhaseDepthCohomologyComplete

/-- A function `g : ZMod 5 → G` whose five values sum to zero is a coboundary, with explicit
witness the partial-sum function `h k = ∑ i < k.val, g i`. -/
private lemma coboundary_of_five_sum_zero {G : Type*} [AddCommGroup G] (g : ZMod 5 → G)
    (hzero : g 0 + g 1 + g 2 + g 3 + g 4 = 0) :
    ∃ h : ZMod 5 → G, ∀ j, g j = h (j + 1) - h j := by
  refine ⟨fun k => ∑ i ∈ Finset.range k.val, g (i : ZMod 5), ?_⟩
  intro j
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by decide +revert
  rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    show _ = ∑ i ∈ Finset.range (ZMod.val _), _ - ∑ i ∈ Finset.range (ZMod.val _), _ <;>
    norm_num [show (0:ZMod 5).val = 0 from rfl, show (1:ZMod 5).val = 1 from rfl,
      show (2:ZMod 5).val = 2 from rfl, show (3:ZMod 5).val = 3 from rfl,
      show (4:ZMod 5).val = 4 from rfl, show (5:ZMod 5).val = 0 from rfl,
      Finset.sum_range_succ, show ((0:ℕ) : ZMod 5) = 0 from rfl,
      show ((1:ℕ) : ZMod 5) = 1 from rfl, show ((2:ℕ) : ZMod 5) = 2 from rfl,
      show ((3:ℕ) : ZMod 5) = 3 from rfl]
  linear_combination (norm := abel) hzero

/-- **Completeness (converse) half of the discrete-cohomology no-go on the 5-cycle.**

If two cochains `c1 c2 : ZMod 5 → G` into an additive commutative group have equal total sum,
then their difference is a coboundary: there is `h : ZMod 5 → G` with
`c1 j - c2 j = h (j + 1) - h j` for every `j : ZMod 5`.

The witness is the partial-sum function `h k = ∑ i < k.val, (c1 i - c2 i)`; the seam at `j = 4`
(where `j + 1 = 0`) closes precisely because the total sum of `c1 - c2` vanishes. -/
theorem coboundary_of_sum_eq {G : Type*} [AddCommGroup G] (c1 c2 : ZMod 5 → G)
    (hs : (Finset.univ.sum c1) = (Finset.univ.sum c2)) :
    ∃ h : ZMod 5 → G, ∀ j, c1 j - c2 j = h (j + 1) - h j := by
  obtain ⟨g, hgdef⟩ : ∃ g : ZMod 5 → G, ∀ j, g j = c1 j - c2 j := ⟨_, fun _ => rfl⟩
  have hsum : Finset.univ.sum g = 0 := by
    simp [hgdef, Finset.sum_sub_distrib, hs]
  rw [Fin.sum_univ_five (f := (g : Fin 5 → G))] at hsum
  obtain ⟨h, hh⟩ := coboundary_of_five_sum_zero g (by linear_combination (norm := abel) hsum)
  exact ⟨h, fun j => (hgdef j) ▸ hh j⟩

end Brockian.PhaseDepthCohomologyComplete

#print axioms Brockian.PhaseDepthCohomologyComplete.coboundary_of_sum_eq

