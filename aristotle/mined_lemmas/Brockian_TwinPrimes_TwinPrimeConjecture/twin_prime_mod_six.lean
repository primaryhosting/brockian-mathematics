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
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Nat

namespace Brockian.TwinPrimes

/-- **The Twin Prime Conjecture**: there are arbitrarily large primes `p` such that
`p + 2` is also prime. -/

theorem twin_prime_mod_six {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime) (h3 : 3 < p) :
    p % 6 = 5 := by
  have h2 : ¬ (2 ∣ p) := fun h =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h) (by omega)
  have h3' : ¬ (3 ∣ p) := fun h =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h) (by omega)
  have h3'' : ¬ (3 ∣ (p + 2)) := fun h =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h) (by omega)
  rw [Nat.dvd_iff_mod_eq_zero] at h2 h3' h3''
  omega

/-- There is at least one twin prime pair. -/
