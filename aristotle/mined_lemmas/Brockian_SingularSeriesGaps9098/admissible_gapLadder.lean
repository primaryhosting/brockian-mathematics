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

theorem admissible_gapLadder {n : ℕ} (hn : 0 < n) : Admissible (gapLadder n) := by
  intro p hp
  by_cases hpn : p ≤ n
  · rw [residueCount_gapLadder_small hn hp hpn]
    exact lt_of_lt_of_le one_lt_two (by exact_mod_cast hp.two_le)
  · have := residueCount_le_card (gapLadder n) p
    rw [card_gapLadder] at this
    omega

/--
**Singular Series Gaps 9098.**

For every `n ≥ 1` the `n`-element gap range
`{0, n!, 2·n!, …, (n-1)·n!}` is an admissible tuple of shifts: it has exactly `n`
elements, it omits a residue class modulo every prime, and consequently every local
factor of the associated Hardy–Littlewood singular series is strictly positive.
This gives, for each `n`, a new admissible gap range extending the
`SingularSeriesGaps` family.
-/
