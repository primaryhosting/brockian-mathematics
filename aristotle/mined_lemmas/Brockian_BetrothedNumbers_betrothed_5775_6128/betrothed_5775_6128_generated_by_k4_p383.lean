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

theorem betrothed_5775_6128_generated_by_k4_p383 :
    Nat.Prime 383 ∧ (383 : ℕ) ≠ 2 ∧ (6128 : ℕ) = 2 ^ 4 * 383 ∧
      σ 1 6128 = (2 ^ (4 + 1) - 1) * (383 + 1) ∧
      (5775 : ℕ) = (2 ^ (4 + 1) - 1) * (383 + 1) - 2 ^ 4 * 383 - 1 ∧
      IsBetrothedPair 5775 (2 ^ 4 * 383) := by
  refine ⟨prime_383, by norm_num, six128_eq, ?_, by norm_num, ?_⟩
  · rw [sigma_one_6128]; norm_num
  · exact betrothed_of_sigma_criterion prime_383 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by rw [sigma_one_5775]; norm_num)

end Brockian.BetrothedNumbers

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

