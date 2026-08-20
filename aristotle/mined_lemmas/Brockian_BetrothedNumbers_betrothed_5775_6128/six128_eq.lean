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

open scoped ArithmeticFunction.sigma

set_option maxRecDepth 100000

namespace Brockian.BetrothedNumbers

/-- Two distinct positive naturals `m ≠ n` form a *betrothed* (quasi-amicable) pair when
each is the sum of the *nontrivial* proper divisors of the other, equivalently
`σ m = σ n = m + n + 1`. -/

lemma six128_eq : (6128 : ℕ) = 2 ^ 4 * 383 := by norm_num

/-- **(5775, 6128) is a betrothed pair.** -/
