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

theorem admissible_image_add_const (S : Finset ℤ) (c : ℤ)
    (h : Admissible S) : Admissible (S.image (· + c)) := by
  intro p hp
  obtain ⟨r, hr⟩ := h p hp
  refine ⟨r + (c : ZMod p), ?_⟩
  intro hmem
  apply hr
  simp only [residueImage, Finset.mem_image, Finset.image_image] at hmem ⊢
  obtain ⟨s, hs, hs2⟩ := hmem
  refine ⟨s, hs, ?_⟩
  simp only [Function.comp_apply, Int.cast_add] at hs2
  exact add_right_cancel hs2

