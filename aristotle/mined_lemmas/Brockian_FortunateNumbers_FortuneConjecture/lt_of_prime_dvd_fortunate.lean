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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FortunateNumbers

open Nat

/-- Existence of a "fortunate offset": for every `n` there is some `m > 1` such that
`n# + m` is prime, where `n#` is the primorial of `n`.  This follows from Bertrand's
postulate applied to `n# + 1`. -/

theorem lt_of_prime_dvd_fortunate {q n : ℕ} (hq : Nat.Prime q) (hdvd : q ∣ fortunate n) :
    n < q := by
  by_contra h
  exact not_dvd_fortunate_of_prime_le hq (Nat.le_of_not_lt h) hdvd

/-- **Unconditional dichotomy.**  For every `n`, the Fortunate number of `n` is either prime,
or it is at least `(n+1)^2`.  (Its least prime factor exceeds `n`, so if it were composite it
would be at least the square of that factor.) -/
