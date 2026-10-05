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

import Mathlib

/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A *unitary divisor* of `n` is a divisor `d` with `gcd d (n / d) = 1`, and `n` is *unitary
perfect* when the sum `σ*(n)` of its unitary divisors equals `2 * n`.  Exactly five unitary
perfect numbers are known:

`6`, `60`, `90`, `87360`, `146361946186458562560000`,

and whether a sixth one exists is an open problem.  This file develops the basic theory
(`σ*` is multiplicative, `σ*(p^a) = 1 + p^a`, the factorization formula), verifies the five
known examples, proves that every unitary perfect number is even, and reduces the existence
of a sixth unitary perfect number to an explicit arithmetic criterion on the odd part.
-/

open Finset

namespace Brockian.UnitaryPerfect

/-- The unitary divisors of `n`: divisors `d` of `n` with `gcd d (n / d) = 1`. -/

theorem isUnitaryPerfect_iff_odd_part {a m : ℕ} (ha : 1 ≤ a) (hm : Odd m) :
    IsUnitaryPerfect (2 ^ a * m) ↔ (1 + 2 ^ a) * usigma m = 2 ^ (a + 1) * m := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have hpos : 0 < 2 ^ a * m := by positivity
  rw [IsUnitaryPerfect, usigma_prime_pow_mul Nat.prime_two (by omega) hm0 hcop]
  constructor
  · rintro ⟨-, h⟩
    rw [h, pow_succ]; ring
  · intro h
    exact ⟨hpos, by rw [h, pow_succ]; ring⟩

/-- **Conditional statement.**  Whether a sixth unitary perfect number exists is an open
problem: only five unitary perfect numbers are known, and no proof of existence (or of
nonexistence) of a further one is known.  What is proved here is the reduction of the
question to a concrete arithmetic search: since every unitary perfect number is even (see
`not_isUnitaryPerfect_of_odd`), the existence of a sixth unitary perfect number follows from
-- and, by `sixthUnitaryPerfect_criterion`, is equivalent to -- the existence of an exponent
`a ≥ 1` and an odd number `m` satisfying `(1 + 2 ^ a) * σ*(m) = 2 ^ (a + 1) * m` with
`2 ^ a * m` not one of the five known unitary perfect numbers. -/
