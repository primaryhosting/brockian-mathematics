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

theorem admissible_image_neg (S : Finset ℤ) (h : Admissible S) :
    Admissible (S.image (fun x => -x)) := by
  intro p hp
  obtain ⟨r, hr⟩ := h p hp
  refine ⟨-r, fun hmem => hr ?_⟩
  simp only [residueImage, Finset.mem_image, Finset.image_image, Function.comp] at hmem ⊢
  obtain ⟨x, hx, hxe⟩ := hmem
  exact ⟨x, hx, by push_cast at hxe ⊢; linear_combination -hxe⟩

