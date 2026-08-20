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

/-- The two-prime ("K2") Goldbach wheel condition at modulus `m`.

Thinking of the residues mod `m` as a wheel, this says that the wheel is *fully covered*
by sums of two prime spokes: every residue class `n` mod `m` can be hit by a sum `p + q`
of two primes, both coprime to `m` (i.e. both lying on the wheel), and with the two primes
taken arbitrarily large.  This is the exact local-at-`m` statement underlying a Goldbach-type
two-prime representation: no residue class mod `m` is obstructed. -/

theorem coprime_of_pos_lt_prime {P a : ℕ} (hP : Nat.Prime P) (h0 : 0 < a) (h : a < P) :
    Nat.Coprime a P := by
  rw [Nat.coprime_comm]
  rw [Nat.Prime.coprime_iff_not_dvd hP]
  intro hdvd
  have := Nat.le_of_dvd h0 hdvd
  omega

/-- **The Goldbach wheel is fully covered at every odd prime modulus.**
For a prime `P > 2`, every residue class mod `P` is the sum of two arbitrarily large primes,
both coprime to `P`. -/
