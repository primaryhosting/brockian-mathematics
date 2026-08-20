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

/-!
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Nat

namespace Brockian.WilsonPrimes

/-- A *Wilson prime* is a prime `p` such that `p ^ 2 ∣ (p - 1)! + 1`, i.e. the congruence
of Wilson's theorem holds modulo `p ^ 2` and not merely modulo `p`. -/

theorem wilsonPrime_iff_zmod {p : ℕ} (hp : p.Prime) :
    WilsonPrime p ↔ (((p - 1)! : ℕ) : ZMod (p ^ 2)) = -1 := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  constructor
  · rintro ⟨-, h⟩
    have h0 : (((p - 1)! + 1 : ℕ) : ZMod (p ^ 2)) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    push_cast at h0
    linear_combination h0
  · intro h
    refine ⟨hp, ?_⟩
    refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
    push_cast
    rw [h]
    ring

/-- Wilson primality as an explicitly decidable congruence condition. -/
