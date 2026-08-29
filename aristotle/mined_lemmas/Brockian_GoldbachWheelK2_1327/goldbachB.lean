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

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace Brockian

/-- `noFactorBelow n k` is `true` exactly when no `d` with `2 ≤ d ≤ k` divides `n`. -/

def goldbachB (n : ℕ) : Bool := wheelPrimes.any (fun p => isPrimeB p && isPrimeB (n - p))

/-- The wheel check for every even number in `[4, 2 * 1327]`. -/
