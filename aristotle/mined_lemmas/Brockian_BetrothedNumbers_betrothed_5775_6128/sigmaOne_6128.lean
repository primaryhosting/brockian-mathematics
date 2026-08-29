/-
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open Finset

/-- The sum-of-divisors function `σ₁ n = ∑_{d ∣ n} d`. -/

theorem sigmaOne_6128 : sigmaOne 6128 = 11904 := by
  decide +kernel

set_option maxRecDepth 10000 in
/-- **Main result.** `(5775, 6128)` is a betrothed (quasi-amicable) pair:
`σ₁ 5775 = σ₁ 6128 = 5775 + 6128 + 1 = 11904`. Verified by kernel reduction. -/
