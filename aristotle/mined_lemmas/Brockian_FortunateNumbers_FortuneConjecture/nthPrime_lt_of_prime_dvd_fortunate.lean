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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FortunateNumbers

open Finset

/-- The `n`-th prime (`nthPrime 0 = 2`, `nthPrime 1 = 3`, ...). -/

theorem nthPrime_lt_of_prime_dvd_fortunate {n q : ℕ} (hq : q.Prime) (hdvd : q ∣ fortunate n) :
    nthPrime n < q :=
  nthPrime_lt_of_prime_dvd (one_lt_fortunate n) (prime_primorialOf_add_fortunate n) hq hdvd

/-- **Unconditional dichotomy.** Each fortunate number is either prime or at least `pₙ₊₁²`. -/
