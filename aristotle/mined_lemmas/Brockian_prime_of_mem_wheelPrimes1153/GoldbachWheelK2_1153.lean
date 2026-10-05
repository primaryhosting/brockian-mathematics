/-
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Brockian

/-- The list of all primes below the wheel modulus `1153`. -/

theorem GoldbachWheelK2_1153 (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 1153) (heven : Even n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨m, rfl⟩ := heven
  have hk : m - 2 ∈ List.range 575 := by
    rw [List.mem_range]; omega
  obtain ⟨p, hp, hq⟩ := wheelPrimes1153_split (m - 2) hk
  have h2 : 2 * (m - 2) + 4 = m + m := by omega
  rw [h2] at hq
  have hq2 := prime_of_mem_wheelPrimes1153 _ hq
  refine ⟨p, m + m - p, prime_of_mem_wheelPrimes1153 p hp, hq2, ?_⟩
  have := hq2.two_le
  omega

end Brockian

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

