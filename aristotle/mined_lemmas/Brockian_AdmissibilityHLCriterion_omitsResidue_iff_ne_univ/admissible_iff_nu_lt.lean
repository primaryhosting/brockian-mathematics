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

theorem admissible_iff_nu_lt (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → nu p H < p := by
  unfold Admissible
  constructor
  · intro h p hp
    letI : NeZero p := ⟨hp.pos.ne'⟩
    exact (omitsResidue_iff_nu_lt p H).mp (h p hp)
  · intro h p hp
    letI : NeZero p := ⟨hp.pos.ne'⟩
    exact (omitsResidue_iff_nu_lt p H).mpr (h p hp)

/-- **The criterion, verbatim.** `H` is admissible iff for every prime `p` the image of
`H` in `ZMod p` has fewer than `p` elements. -/
