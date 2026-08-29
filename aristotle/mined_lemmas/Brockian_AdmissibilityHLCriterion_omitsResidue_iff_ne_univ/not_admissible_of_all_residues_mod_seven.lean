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

theorem not_admissible_of_all_residues_mod_seven :
    ¬ Admissible ({0, 1, 9, 10, 11, 12, 20} : Finset ℤ) := by
  intro h
  obtain ⟨r, hr⟩ := h 7 (by norm_num)
  exact hr (by revert r; decide)

/-- Membership in the mod-`p` residue image of an affine image of `S`. -/
