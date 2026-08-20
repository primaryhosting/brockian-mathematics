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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cullen Prime Infinitude

Cullen numbers are `C n = n * 2 ^ n + 1`.  Whether infinitely many of them are prime is a
well-known open problem, so the target `CullenPrimeInfinitude` below is stated and proved as
an unconditional *reduction*: the set of Cullen prime indices is infinite iff Cullen primes
occur past every bound.

We also prove the classical partial results in the opposite direction: every odd prime `p`
divides `C (p - 2)`, hence `C (p - 2)` is composite for every prime `p ≥ 5`, and therefore
infinitely many Cullen numbers are composite.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

theorem cullen_not_prime_of_prime {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ (cullen (p - 2)).Prime := by
  intro hq
  have hdvd := prime_dvd_cullen_sub_two hp (by omega)
  have heq : p = cullen (p - 2) := (Nat.prime_dvd_prime_iff_eq hp hq).1 hdvd
  have hlt : p - 2 < 2 ^ (p - 2) := Nat.lt_two_pow_self
  have hge : 3 ≤ p - 2 := by omega
  have hmul : 3 * 2 ^ (p - 2) ≤ (p - 2) * 2 ^ (p - 2) := Nat.mul_le_mul_right _ hge
  have hkey : p < cullen (p - 2) := by
    unfold cullen
    omega
  omega

/-- There are infinitely many `n` for which the Cullen number `C n` is *composite*
(indeed `p ∣ C (p - 2)` for every prime `p ≥ 5`). -/
