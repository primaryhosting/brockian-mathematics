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

theorem firstNinePrimeOffsets_not_admissible :
    ¬ Admissible ({0, 1, 3, 5, 9, 11, 15, 17, 21} : Finset ℤ) := by
  intro h
  obtain ⟨r, hr⟩ := h 2 Nat.prime_two
  revert hr
  revert r
  decide

