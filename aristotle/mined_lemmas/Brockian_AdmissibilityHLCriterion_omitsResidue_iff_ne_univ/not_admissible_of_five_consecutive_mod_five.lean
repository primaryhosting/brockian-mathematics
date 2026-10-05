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

theorem not_admissible_of_five_consecutive_mod_five :
    ¬ Admissible ({0, 1, 2, 3, 4} : Finset ℤ) := by
  intro h
  obtain ⟨r, hr⟩ := h 5 (by norm_num)
  revert hr
  revert r
  decide

/-- Negation acts as a bijection on residues mod every prime, so it preserves
admissibility. -/
