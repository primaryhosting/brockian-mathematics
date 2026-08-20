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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BrocardGap

open Finset

/-- **Oppermann's conjecture**: for every `m > 1` there is a prime strictly between
`m² - m` and `m²`, and a prime strictly between `m²` and `m² + m`. -/

theorem brocardGap_one :
    4 ≤ primesBetween (Nat.nth Nat.Prime 1 * Nat.nth Nat.Prime 1)
      (Nat.nth Nat.Prime 2 * Nat.nth Nat.Prime 2) := by
  rw [Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
  exact four_le_primesBetween_nine_twentyfive

end Brockian.BrocardGap

