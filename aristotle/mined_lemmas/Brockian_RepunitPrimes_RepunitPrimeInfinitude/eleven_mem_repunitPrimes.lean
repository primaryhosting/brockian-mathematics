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
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RepunitPrimes

/-- The `n`-th base-ten repunit: the number `11…1` with `n` digits equal to `1`. -/

theorem eleven_mem_repunitPrimes : 11 ∈ repunitPrimes :=
  ⟨by norm_num, ⟨2, repunit_two.symm⟩⟩

/--
**Conditional reduction of the repunit-prime infinitude conjecture.**

Assuming the (open) hypothesis that repunit primes occur with arbitrarily large index,
the set of repunit primes is infinite.

By `prime_of_repunit_prime` such indices are necessarily prime, so the hypothesis says
exactly that there are infinitely many primes `n` for which the `n`-digit repunit is prime.
-/
