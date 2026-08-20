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

/-!
## Overview

Let `n#` denote the primorial of `n` (the product of all primes `≤ n`).  The *fortunate number*
`fortunate n` is the smallest integer `m > 1` such that `n# + m` is prime.  Reo Fortune
conjectured that `fortunate n` is always prime; this is an open problem.

What is proved here:

* `Brockian.FortunateNumbers.lt_of_prime_dvd_fortunate` (unconditional): every prime factor of
  `fortunate n` is strictly larger than `n`.  Indeed, a prime `q ≤ n` divides `n#`, so if `q`
  also divided `m` it would divide `n# + m`, which is prime and larger than `q`.
* `Brockian.FortunateNumbers.fortunate_prime_of_le_sq` (unconditional): consequently, if
  `fortunate n ≤ n ^ 2` then `fortunate n` is prime, since a composite number has a prime factor
  whose square is at most the number itself.
* `Brockian.FortunateNumbers.FortuneConjecture` (conditional reduction): Fortune's conjecture
  follows from the size bound `fortunate n ≤ n ^ 2` for all `n ≥ 2`.  The cases `n = 0, 1` are
  handled unconditionally (there `fortunate n = 2`).

Some concrete values are also computed and verified (`fortunate 2 = 3`, `fortunate 3 = 5`,
`fortunate 5 = 7`), which shows in particular that the hypothesis of `FortuneConjecture` is not
vacuous in the small cases.
-/

namespace Brockian
namespace FortunateNumbers

open Nat

/-- The set of offsets `m > 1` for which `n# + m` is prime. -/

theorem offsets_nonempty (n : ℕ) : (offsets n).Nonempty := by
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (primorial n + 2)
  refine ⟨p - primorial n, by omega, ?_⟩
  have h : primorial n + (p - primorial n) = p := by omega
  rw [h]
  exact hpp

/-- The *fortunate number* of `n`: the smallest `m > 1` such that `n# + m` is prime. -/
