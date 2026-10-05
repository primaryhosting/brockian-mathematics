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

def noFactorBelow (n : ℕ) : ℕ → Bool
  | 0 => true
  | 1 => true
  | (k + 2) => (n % (k + 2) != 0) && noFactorBelow n (k + 1)

/-- A trial-division primality test, correct for `n < 2704 = 52 ^ 2`. -/
