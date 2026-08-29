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
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RepunitPrimes

/-- The `n`-th base-ten repunit `Rₙ = 1 + 10 + ⋯ + 10ⁿ⁻¹ = (10ⁿ - 1)/9`. -/

lemma repunit_odd {n : ℕ} (hn : 0 < n) : ¬ (2 ∣ repunit n) := by
  intro h
  have h9 := nine_mul_repunit_add_one n
  have h2 : (2:ℕ) ∣ 10 ^ n := dvd_pow (by norm_num) hn.ne'
  omega

/-- A repunit is congruent to its index modulo `3` (its digit sum is `n`). -/
