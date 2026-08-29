/-!
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- The list of primes used as spokes of the Goldbach wheel of modulus `631`. -/

theorem GoldbachWheelK2_631_zmod (r : ZMod 631) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ (p : ZMod 631) + (q : ZMod 631) = r := by
  obtain ⟨p, q, hp, hq, h⟩ := GoldbachWheelK2_631 r.val
  refine ⟨p, q, hp, hq, ?_⟩
  have : ((p + q : ℕ) : ZMod 631) = ((r.val : ℕ) : ZMod 631) := (ZMod.natCast_eq_natCast_iff _ _ _).2 h
  simpa using this

end Brockian

