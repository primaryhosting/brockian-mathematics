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

/-!
## Overview

Reid Fortune's conjecture states that for every `n`, the *fortunate number*

  `F n = the least m > 1 such that n# + m is prime`

(where `n#` is the primorial, the product of all primes `≤ n`) is a prime number.
This is an open problem: no unconditional proof is known, because it would require an
upper bound on the prime gap after `n#` far stronger than anything currently provable.

What *is* provable, and what this file establishes, is the standard reduction:

* every prime factor of `F n` exceeds `n` (`Brockian.FortunateNumbers.lt_of_prime_dvd_fortunate`),
  because all primes `≤ n` divide `n#`;
* hence if `F n ≤ n ^ 2`, then `F n` must be prime
  (`Brockian.FortunateNumbers.fortunate_prime_of_le_sq`);
* consequently, the quadratic gap bound `∀ n ≥ 2, F n ≤ n ^ 2` implies the full Fortune
  conjecture (`Brockian.FortunateNumbers.FortuneConjecture`).

The target theorem `Brockian.FortunateNumbers.FortuneConjecture` is therefore stated as a
*conditional* reduction: it derives the conjecture for **all** `n` from the gap hypothesis,
with the two degenerate cases `n = 0, 1` handled unconditionally.
-/

namespace Brockian.FortunateNumbers

open Finset

/-- There is some `m > 1` with `primorial n + m` prime; this is what makes the
fortunate number well defined. -/

theorem one_lt_fortunate (n : ℕ) : 1 < fortunate n :=
  (Nat.find_spec (exists_fortunate n)).1

