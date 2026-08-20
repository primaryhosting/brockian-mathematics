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
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Nat

namespace Brockian.WilsonPrimes

/-- A *Wilson prime* is a prime `p` such that `p ^ 2 ∣ (p - 1)! + 1`
(equivalently, Wilson's congruence `(p-1)! ≡ -1` holds modulo `p ^ 2`). -/

theorem isWilsonPrime_iff_dvd_wilsonQuotient {p : ℕ} (hp : p.Prime) :
    IsWilsonPrime p ↔ p ∣ wilsonQuotient p := by
  constructor
  · rintro ⟨-, hd⟩
    rw [← mul_wilsonQuotient hp, pow_two] at hd
    exact (mul_dvd_mul_iff_left hp.pos.ne').mp hd
  · intro hd
    refine ⟨hp, ?_⟩
    rw [← mul_wilsonQuotient hp, pow_two]
    exact mul_dvd_mul_left p hd

/-- Wilson prime condition expressed as a congruence in `ZMod (p ^ 2)`. -/
