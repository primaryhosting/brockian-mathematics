/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, stated from first principles:
`n` is at least `2` and its only divisors are `1` and `n`. -/

theorem goldbachWheelK2_1153_nat_prime :
    ∀ n : ℕ, 4 ≤ n → n ≤ 1153 → Even n →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  intro n hn4 hn1153 hev
  obtain ⟨k, hk⟩ := hev
  obtain ⟨p, q, hp, hq, hpq⟩ := GoldbachWheelK2_1153 n hn4 hn1153 (by omega)
  exact ⟨p, q, isPrime_iff_nat_prime.mp hp, isPrime_iff_nat_prime.mp hq, hpq⟩

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

