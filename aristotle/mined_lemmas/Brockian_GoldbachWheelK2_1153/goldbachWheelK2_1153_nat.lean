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

namespace Brockian

/-- The *wheel* at modulus `M` is the set of residue classes modulo `M` that are coprime to `M`,
i.e. the units of `ZMod M`.

`M` is a *Goldbach wheel modulus of order 2* when the wheel is a `2`-fold additive basis of
`ZMod M`: every residue class modulo `M` is a sum of two classes lying on the wheel.

This is exactly the local (mod `M`) condition one has to check before a modulus `M` can be
used as a wheel in a two-prime (Goldbach-type) sieve: if `n` is a sum of two primes not dividing
`M`, then its class mod `M` must be a sum of two units. -/

theorem goldbachWheelK2_1153_nat (n : ℕ) :
    ∃ a b : ℕ, Nat.Coprime a 1153 ∧ Nat.Coprime b 1153 ∧ (a + b) % 1153 = n % 1153 := by
  obtain ⟨a, b, ha, hb, hab⟩ := GoldbachWheelK2_1153 (n : ZMod 1153)
  refine ⟨a.val, b.val, ?_, ?_, ?_⟩
  · rw [← ZMod.isUnit_iff_coprime]
    simpa using ha
  · rw [← ZMod.isUnit_iff_coprime]
    simpa using hb
  · have hc : ((a.val + b.val : ℕ) : ZMod 1153) = (n : ZMod 1153) := by
      push_cast [ZMod.natCast_val, ZMod.cast_id]
      exact hab
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hc

/-- For a prime modulus `p`, every residue class has at least `p - 2` representations as an
ordered sum of two classes coprime to `p`. -/
