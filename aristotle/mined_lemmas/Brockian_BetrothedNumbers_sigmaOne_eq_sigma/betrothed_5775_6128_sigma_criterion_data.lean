import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

set_option maxRecDepth 100000

namespace Brockian.BetrothedNumbers

/-- The sum-of-divisors function `σ₁`. -/

theorem betrothed_5775_6128_sigma_criterion_data :
    Nat.Prime 383 ∧ 6128 = 2 ^ 4 * 383 ∧
      sigmaOne (2 ^ 4 * 383) = (2 ^ (4 + 1) - 1) * (383 + 1) ∧
      sigmaOne 5775 = (2 ^ (4 + 1) - 1) * (383 + 1) ∧
      (2 ^ (4 + 1) - 1) * (383 + 1) = 5775 + 6128 + 1 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, by norm_num⟩
  · rw [sigmaOne_two_pow_mul_prime (by norm_num) (by norm_num)]
  · rw [sigmaOne_5775]; norm_num

end Criterion

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

