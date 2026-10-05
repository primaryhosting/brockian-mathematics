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

noncomputable def localFactor (H : Finset ℤ) (p : ℕ) : ℝ :=
  (1 - (residueCount H p : ℝ) / p) * (1 - 1 / (p : ℝ)) ^ (-(H.card : ℤ))

/-- The number of occupied residue classes never exceeds the size of the tuple. -/
