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

theorem prime_dvd_three_primes (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) {s : ℕ}
    (hs : s.Prime) (hdvd : s ∣ p * q * r) : s = p ∨ s = q ∨ s = r := by
  rcases (Nat.Prime.dvd_mul hs).1 hdvd with h | h
  · rcases (Nat.Prime.dvd_mul hs).1 h with h' | h'
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hs hp).1 h')
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hs hq).1 h'))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hs hr).1 h))

/-- A product of three distinct primes is squarefree. -/
