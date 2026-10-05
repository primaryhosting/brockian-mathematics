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

theorem not_admissible_zero_two_four : ¬ Admissible ({0, 2, 4} : Finset ℤ) := by
  intro h
  have h3 := (admissible_iff_nu_lt _).mp h 3 (by norm_num)
  have hnu3 : nu 3 ({0, 2, 4} : Finset ℤ) = 3 := by decide
  omega

/-- The nine-element offset set `{0, 1, 3, 5, 9, 11, 15, 17, 21}` is not admissible:
it covers both residue classes mod `2`. -/
