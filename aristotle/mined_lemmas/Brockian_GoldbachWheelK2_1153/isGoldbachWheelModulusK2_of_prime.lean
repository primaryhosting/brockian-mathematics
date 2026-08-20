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

theorem isGoldbachWheelModulusK2_of_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    IsGoldbachWheelModulusK2 p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have h2' : (2 : ZMod p) ≠ 0 := by
    have hcast : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
    simpa using hcast
  intro r
  by_cases h : r = 1
  · refine ⟨2, -1, isUnit_iff_ne_zero.mpr h2', isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr h1), ?_⟩
    rw [h]; ring
  · refine ⟨1, r - 1, isUnit_one, ?_, by ring⟩
    exact isUnit_iff_ne_zero.mpr fun hc => h (sub_eq_zero.mp hc)

/-- **New wheel modulus.** `1153` is a Goldbach wheel modulus of order `2`: every residue class
modulo `1153` is the sum of two residue classes coprime to `1153`. -/
