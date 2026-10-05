/-
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian

/-- `noDiv n k` is `true` when no `d` with `2 ≤ d ≤ k` divides `n`. -/

def goldbachSplit (m : ℕ) : Bool :=
  wheelPrimes.any (fun p => isPrimeB p && decide (p < m) && isPrimeB (m - p))

