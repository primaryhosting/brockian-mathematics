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

theorem admissible_of_subset {S T : Finset ℤ} (h : Admissible S)
    (hT : T ⊆ S) : Admissible T := by
  intro p hp
  obtain ⟨r, hr⟩ := h p hp
  exact ⟨r, fun hmem => hr (residueImage_subset p hT hmem)⟩

