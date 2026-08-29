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

theorem isUnitaryPerfect_of_mem_known {n : ℕ} (hn : n ∈ knownUnitaryPerfect) :
    IsUnitaryPerfect n := by
  simp only [knownUnitaryPerfect, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact isUnitaryPerfect_six
  · exact isUnitaryPerfect_sixty
  · exact isUnitaryPerfect_ninety
  · exact isUnitaryPerfect_87360
  · exact isUnitaryPerfect_big

/-! ### Every unitary perfect number is even -/

/-- There is no odd unitary perfect number: if `n` is odd with `k` distinct prime factors,
then `2 ^ k ∣ σ*(n)`, which forces `k ≤ 1`, and both remaining cases are impossible. -/
