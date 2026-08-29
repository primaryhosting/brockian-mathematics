/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

/-- `residueCount H p` is the number of distinct residue classes modulo `p`
occupied by the shifts in the tuple `H`. -/

theorem admissible_of_small_primes {H : Finset ℤ}
    (h : ∀ p : ℕ, p.Prime → p ≤ H.card → residueCount H p < p) : Admissible H := by
  intro p hp
  by_cases hle : p ≤ H.card
  · exact h p hp hle
  · exact lt_of_le_of_lt (residueCount_le_card H p) (by omega)

/-- Every local factor of an admissible tuple is strictly positive. -/
