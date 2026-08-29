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

theorem omitsResidue_iff_nu_lt (p : ℕ) [NeZero p] (H : Finset ℤ) :
    OmitsResidue p H ↔ nu p H < p := by
  rw [omitsResidue_iff_ne_univ]
  have h : (residueImage p H).card < Fintype.card (ZMod p)
      ↔ residueImage p H ≠ Finset.univ :=
    Finset.card_lt_iff_ne_univ _
  rw [ZMod.card] at h
  exact h.symm

/-- **The Hardy–Littlewood admissibility criterion (ν form).** A finite integer tuple is
admissible iff at every prime it occupies fewer than `p` residue classes. -/
