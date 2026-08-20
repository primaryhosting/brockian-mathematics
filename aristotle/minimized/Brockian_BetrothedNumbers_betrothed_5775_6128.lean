/-
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxRecDepth 100000

namespace Brockian.BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Two distinct positive naturals `m ≠ n` form a *betrothed* (quasi-amicable) pair when the
sum of the proper divisors of each, excluding `1`, gives the other; equivalently
`σ 1 m = σ 1 n = m + n + 1`. -/

theorem sigma_one_6128 : σ 1 6128 = 11904 := by
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  decide

/-- **(5775, 6128) is a betrothed (quasi-amicable) pair.** -/
