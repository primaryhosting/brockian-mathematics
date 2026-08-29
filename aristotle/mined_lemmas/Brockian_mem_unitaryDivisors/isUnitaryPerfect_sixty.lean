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

/-
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd d (n / d) = 1`. -/

theorem isUnitaryPerfect_sixty : IsUnitaryPerfect 60 := by
  refine ⟨by norm_num, ?_⟩
  have h4 : usigma (2 ^ 2) = 2 ^ 2 + 1 := usigma_prime_pow (by norm_num) (by norm_num)
  rw [show (60 : ℕ) = 2 ^ 2 * (3 * 5) by norm_num, usigma_mul_of_coprime (by norm_num),
    usigma_mul_of_coprime (by norm_num), h4, usigma_prime (by norm_num),
    usigma_prime (by norm_num)]
  norm_num

