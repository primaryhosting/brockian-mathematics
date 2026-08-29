import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Brockian

/-- The gap window: the integers of the range `[1450, 1460]`. -/

noncomputable def nu (H : Finset ℤ) (p : ℕ) : ℕ := (H.image (Int.cast : ℤ → ZMod p)).card

/-- A finite set of integers is *admissible* if for every prime `p` it misses at least one
residue class mod `p`. -/
