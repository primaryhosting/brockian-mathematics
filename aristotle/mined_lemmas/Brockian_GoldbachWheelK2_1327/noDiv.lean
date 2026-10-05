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

def noDiv (n : ℕ) : ℕ → Bool
  | 0 => true
  | 1 => true
  | (d + 2) => (n % (d + 2) != 0) && noDiv n (d + 1)

/-- A trial–division primality test, sound for `n ≤ 2703` (`51 = ⌊√2703⌋`). -/
