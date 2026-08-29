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

theorem admissible_iff_card_image_lt (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → (H.image (fun n : ℤ => (n : ZMod p))).card < p :=
  admissible_iff_nu_lt H

/-- **The finiteness reduction.** Admissibility only needs checking at primes `p ≤ |H|`:
for a prime `p > |H|` we have `ν_p(H) ≤ |H| < p` automatically.  Hence admissibility is
decided by finitely many local checks. -/
