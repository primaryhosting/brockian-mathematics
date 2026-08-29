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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CarmichaelKorselt

open Nat

/-- `IsCarmichael n` : `n` is a Carmichael number, i.e. `n` is composite (greater than one and
not prime) and satisfies the conclusion of Fermat's little theorem for every base coprime
to `n`. -/

theorem card_primeFactors_three_primes (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : (p * q * r).primeFactors.card = 3 := by
  have hpf : (p * q * r).primeFactors = {p, q, r} := by
    rw [Nat.primeFactors_mul (Nat.mul_ne_zero hp.pos.ne' hq.pos.ne') hr.pos.ne',
      Nat.primeFactors_mul hp.pos.ne' hq.pos.ne', hp.primeFactors, hq.primeFactors,
      hr.primeFactors]
    ext x; simp [or_assoc]
  rw [hpf]
  rw [Finset.card_insert_of_notMem (by simp [hpq, hpr]),
    Finset.card_insert_of_notMem (by simpa using hqr), Finset.card_singleton]

/-- Korselt's criterion for a product of three distinct primes. -/
