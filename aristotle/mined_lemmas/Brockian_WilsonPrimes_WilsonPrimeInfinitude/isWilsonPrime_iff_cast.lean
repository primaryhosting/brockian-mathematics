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

/-!
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Nat

namespace Brockian.WilsonPrimes

/-- A *Wilson prime* is a prime `p` with `p ^ 2 ∣ (p - 1)! + 1`
(the ordinary Wilson congruence `p ∣ (p-1)! + 1` holds for every prime). -/

theorem isWilsonPrime_iff_cast {p : ℕ} :
    IsWilsonPrime p ↔ p.Prime ∧ ((((p - 1)! : ℕ) : ZMod (p ^ 2)) = -1) := by
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    have h0 : (((p - 1)! + 1 : ℕ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).2 h
    push_cast at h0 ⊢
    linear_combination h0
  · intro h
    refine (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).1 ?_
    push_cast at h ⊢
    linear_combination h

/-! ## The known Wilson primes -/

set_option maxRecDepth 10000 in
