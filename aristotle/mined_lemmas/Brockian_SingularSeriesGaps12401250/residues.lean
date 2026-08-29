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

def residues (H : Finset ℤ) (p : ℕ) : Finset (ZMod p) :=
  H.image (fun h : ℤ => (h : ZMod p))

/-- A finite tuple of integers is *admissible* if for every prime `p` it fails to
cover all residue classes modulo `p`. -/
