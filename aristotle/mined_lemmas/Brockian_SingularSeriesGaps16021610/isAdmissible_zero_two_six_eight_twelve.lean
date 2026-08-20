/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- A finite set of non-negative integers `H` is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuple conjecture) if for every prime `p` the elements of `H`
do not cover all residue classes modulo `p`.  Equivalently, the local factor of the
singular series `𝔖(H)` attached to `H` is non-zero at every prime. -/

theorem isAdmissible_zero_two_six_eight_twelve :
    IsAdmissible ({0, 2, 6, 8, 12} : Finset ℕ) := by
  intro p hp
  rcases lt_or_ge p 6 with h | h
  · interval_cases p <;> revert hp <;> decide
  · have h6 : ({0, 2, 6, 8, 12} : Finset ℕ).card < 6 := by decide
    exact exists_missing_residue_of_card_lt (h6.trans_le h)

/-- The admissible gap range: the tuple `{0, 2, 6, 8, 12}` has `5` elements, minimum `0`,
maximum `12`, and hence diameter `12`. -/
