import Mathlib

set_option autoImplicit false

open Finset

/-
  Context module `Brockian.AdmissibilityHLCriterion`.

  The two corpus lemmas `admissible_iff_exists_avoiding_start` and
  `admissible_iff_count_pos` are omitted here because they refer to the auxiliary
  modules `Brockian.AdmissibilityKTuple` / `Brockian.AdmissibilityCriterionScaffold`,
  which are not part of this project; nothing below uses them.
-/

namespace Brockian.AdmissibilityHLCriterion

/-- The residue classes mod `p` occupied by a finite integer tuple `H`. -/

theorem admissible_image_affine (a b : ℤ) {S : Finset ℤ}
    (h : Admissible S) : Admissible (S.image (fun x => a * x + b)) := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases ha : (a : ZMod p) = 0
  · refine ⟨(b : ZMod p) + 1, ?_⟩
    rw [mem_residueImage_image_affine]
    rintro ⟨x, -, hxe⟩
    rw [ha, zero_mul, zero_add] at hxe
    exact one_ne_zero (α := ZMod p) (by linear_combination -hxe)
  · obtain ⟨r, hr⟩ := h p hp
    refine ⟨(a : ZMod p) * r + (b : ZMod p), ?_⟩
    rw [mem_residueImage_image_affine]
    rintro ⟨x, hx, hxe⟩
    refine hr ?_
    have hrx : (x : ZMod p) = r := by
      have : (a : ZMod p) * ((x : ZMod p) - r) = 0 := by linear_combination hxe
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd h1 ha
      · exact sub_eq_zero.mp h1
    rw [← hrx]
    exact Finset.mem_image_of_mem _ hx

end Brockian.AdmissibilityHLCriterion

