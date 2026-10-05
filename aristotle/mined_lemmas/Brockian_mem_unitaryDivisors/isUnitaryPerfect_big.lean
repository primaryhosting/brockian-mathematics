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

theorem isUnitaryPerfect_big : IsUnitaryPerfect 146361946186458562560000 := by
  refine ⟨by norm_num, ?_⟩
  have h2 : usigma (2 ^ 18) = 2 ^ 18 + 1 := usigma_prime_pow (by norm_num) (by norm_num)
  have h5 : usigma (5 ^ 4) = 5 ^ 4 + 1 := usigma_prime_pow (by norm_num) (by norm_num)
  rw [show (146361946186458562560000 : ℕ) =
      2 ^ 18 * (3 * (5 ^ 4 * (7 * (11 * (13 * (19 * (37 * (79 * (109 * (157 * 313))))))))))
      by norm_num]
  rw [usigma_mul_of_coprime (by norm_num), usigma_mul_of_coprime (by norm_num),
    usigma_mul_of_coprime (by norm_num), usigma_mul_of_coprime (by norm_num),
    usigma_mul_of_coprime (by norm_num), usigma_mul_of_coprime (by norm_num),
    usigma_mul_of_coprime (by norm_num), usigma_mul_of_coprime (by norm_num),
    usigma_mul_of_coprime (by norm_num), usigma_mul_of_coprime (by norm_num),
    usigma_mul_of_coprime (by norm_num), h2, h5, usigma_prime (by norm_num),
    usigma_prime (by norm_num), usigma_prime (by norm_num), usigma_prime (by norm_num),
    usigma_prime (by norm_num), usigma_prime (by norm_num), usigma_prime (by norm_num),
    usigma_prime (by norm_num), usigma_prime (by norm_num), usigma_prime (by norm_num)]
  norm_num

/-- **Conditional reduction for the existence of a sixth unitary perfect number.**

Whether a sixth unitary perfect number exists is an open problem; only five are known,
namely `6`, `60`, `90`, `87360` and `146361946186458562560000`.  This theorem is the
conditional statement: if some unitary perfect number is different from all five known ones,
then there are (at least) six unitary perfect numbers.  The five known ones are proved to be
unitary perfect unconditionally (see `isUnitaryPerfect_six`, ..., `isUnitaryPerfect_big`). -/
