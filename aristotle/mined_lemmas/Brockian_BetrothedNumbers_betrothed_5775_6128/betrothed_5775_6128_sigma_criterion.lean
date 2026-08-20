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

theorem betrothed_5775_6128_sigma_criterion :
    Nat.Prime 383 ∧ (6128 : ℕ) = 2 ^ 4 * 383 ∧
      σ 1 6128 = (2 ^ (4 + 1) - 1) * (383 + 1) ∧
      σ 1 5775 = (2 ^ (4 + 1) - 1) * (383 + 1) ∧
      (2 ^ (4 + 1) - 1) * (383 + 1) = 5775 + 6128 + 1 := by
  have hp : Nat.Prime 383 := by norm_num
  refine ⟨hp, by norm_num, ?_, ?_, by norm_num⟩
  · have h := sigma_one_two_pow_mul_prime (k := 4) hp (by norm_num)
    rw [show (6128 : ℕ) = 2 ^ 4 * 383 by norm_num, h]
  · rw [sigma_one_5775]; norm_num

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

