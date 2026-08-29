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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.FortunateNumbers

open Finset

/-! ## The Fortunate numbers

For a natural number `n`, let `n#` be the primorial of `n` (the product of all primes `≤ n`,
`primorial` in Mathlib).  The *Fortunate number* of `n` is the least `m ≥ 2` such that
`n# + m` is prime.  Fortune's conjecture asserts that every Fortunate number is prime.

The conjecture is open.  What is proved here is:

* every Fortunate number of `n` is coprime to `n#`, i.e. has no prime factor `≤ n`
  (`not_dvd_fortunate`, `lt_minFac_fortunate`);
* consequently, in contrapositive form, a *composite* Fortunate number of `n` must be
  at least `(n+1)^2` (`sq_le_fortunate_of_not_prime`);
* hence the conditional reduction `FortuneConjecture`: Fortune's conjecture follows from the
  (also conjectural, but purely quantitative) bound `fortunate n < (n+1)^2` for `n ≥ 2`.
-/

/-- There is always some `m ≥ 2` with `n# + m` prime: pick a prime `q ≥ n# + 2`. -/

theorem not_dvd_fortunate {p n : ℕ} (hp : Nat.Prime p) (hpn : p ≤ n) : ¬ p ∣ fortunate n := by
  intro hdvd
  have hP : p ∣ primorial n := prime_dvd_primorial hp hpn
  have hsum : p ∣ primorial n + fortunate n := Nat.dvd_add hP hdvd
  have hprime := prime_primorial_add_fortunate n
  have hpe : p = primorial n + fortunate n :=
    ((Nat.Prime.eq_one_or_self_of_dvd hprime p hsum).resolve_left hp.ne_one)
  have hple : p ≤ primorial n := Nat.le_of_dvd (primorial_pos n) hP
  have := two_le_fortunate n
  lia

/-- The least prime factor of the Fortunate number of `n` exceeds `n`. -/
