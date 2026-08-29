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

namespace Brockian
namespace RepunitPrimes

/-- The `n`-th repunit: the base-ten number consisting of `n` digits `1`,
i.e. `repunit n = (10 ^ n - 1) / 9`. -/

lemma repunitPrimes_nonempty : (11 : ℕ) ∈ repunitPrimes :=
  ⟨by decide, 2, rfl⟩

/--
**Repunit Prime Infinitude (conditional reduction).**

Assuming the arithmetic hypothesis that repunit primes occur with arbitrarily large index
(`∀ N, ∃ n > N, repunit n is prime`) — which is the content of the open conjecture — the set
of repunit primes is infinite.

The reduction is genuine: since `repunit` is strictly monotone, distinct indices give distinct
primes, so unboundedness of the index set yields an infinite set of primes.
-/
