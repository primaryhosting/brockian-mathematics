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

theorem admissible_zero_two : Admissible ({0, 2} : Finset ℤ) := by
  rw [admissible_iff_nu_lt_of_le_card]
  intro p hp hle
  have hcard : ({0, 2} : Finset ℤ).card = 2 := by decide
  rw [hcard] at hle
  have hp2 : p = 2 := le_antisymm hle hp.two_le
  subst hp2
  decide

/-- **COMPUTATION.** `{0, 2, 4}` is inadmissible: modulo 3 it occupies all three residue
classes (`ν_3 = 3`), so it omits none. -/
