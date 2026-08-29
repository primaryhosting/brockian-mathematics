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

lemma residues_pair (d : ℤ) (p : ℕ) :
    residues ({0, d} : Finset ℤ) p = {0, (d : ZMod p)} := by
  classical
  by_cases h : (0 : ℤ) = d
  · subst h
    simp [residues]
  · simp [residues]

/-- **Admissible gaps.** The pair `{0, d}` is admissible exactly when `d` is even. -/
