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

theorem exists_two_le_prime_primorial_add (n : ℕ) :
    ∃ m, 2 ≤ m ∧ Nat.Prime (primorial n + m) := by
  obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (primorial n + 2)
  refine ⟨q - primorial n, by lia, ?_⟩
  have : primorial n + (q - primorial n) = q := by lia
  rw [this]
  exact hqp

/-- The Fortunate number of `n`: the least `m ≥ 2` such that `n# + m` is prime. -/
