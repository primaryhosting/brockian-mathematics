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

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd d (n / d) = 1`. -/

theorem not_isPrimePow_of_isUnitaryPerfect {n : ℕ} (h : IsUnitaryPerfect n) :
    ¬ IsPrimePow n := by
  rintro hpp
  obtain ⟨p, k, hp, hk, rfl⟩ := isPrimePow_nat_iff _ |>.1 hpp
  obtain ⟨-, hperf⟩ := h
  rw [usigma_prime_pow hp (by omega)] at hperf
  have h1 : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
  omega

/-- The (open) statement that a sixth unitary perfect number exists. -/
