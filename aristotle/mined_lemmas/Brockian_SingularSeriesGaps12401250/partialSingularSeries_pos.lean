/-
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Key Mathlib ingredients used: `Finset.card_image_le` (a tuple occupies at most `#H`
residue classes, so only primes `p ≤ #H` can obstruct admissibility),
`ZMod.intCast_zmod_eq_zero_iff_dvd` and `even_iff_two_dvd` (the prime `2` analysis),
`Finset.prod_pos` and `zpow_pos` (positivity of the singular series).
-/

open Finset

namespace Brockian

/-- The set of residue classes modulo `p` occupied by the integer tuple `H`. -/

theorem partialSingularSeries_pos {H : Finset ℤ} (hH : Admissible H) (N : ℕ) :
    0 < partialSingularSeries H N := by
  refine Finset.prod_pos ?_
  intro p hp
  exact localFactor_pos hH (Finset.mem_filter.1 hp).2

/-- **Singular Series Gaps 12401250.**

Within the gap range `1240 ≤ d ≤ 1250`, the admissible gaps `d` — i.e. those for which the
pair `{0, d}` is an admissible tuple — are exactly the even ones, namely
`1240, 1242, 1244, 1246, 1248, 1250`; and for each of these gaps every partial
Hardy–Littlewood singular series of the corresponding pair is strictly positive. -/
