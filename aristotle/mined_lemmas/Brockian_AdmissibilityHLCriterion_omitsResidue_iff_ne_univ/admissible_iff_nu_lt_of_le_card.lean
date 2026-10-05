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

theorem admissible_iff_nu_lt_of_le_card (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → p ≤ H.card → nu p H < p := by
  rw [admissible_iff_nu_lt]
  constructor
  · intro h p hp _
    exact h p hp
  · intro h p hp
    by_cases hle : p ≤ H.card
    · exact h p hp hle
    · push_neg at hle
      calc nu p H ≤ H.card := Finset.card_image_le
        _ < p := hle

/-- **COMPUTATION.** `{0, 2}` is admissible.  By the finiteness reduction only the prime
`p = 2` needs checking, and mod 2 the tuple occupies a single class (`ν_2 = 1 < 2`). -/
