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

open Finset

/-- The `n`-th repunit: the number written with `n` copies of the digit `1` in base ten,
i.e. `repunit n = (10 ^ n - 1) / 9 = ∑_{i < n} 10 ^ i`. -/

theorem repunitPrimeIndices_eq :
    RepunitPrimeIndices = {n | Nat.Prime n ∧ Nat.Prime (repunit n)} := by
  ext n
  exact ⟨fun h => ⟨prime_index_of_repunit_prime h, h⟩, fun h => h.2⟩

/--
**Repunit prime infinitude, reduced to prime indices.**

Whether there are infinitely many repunit primes is an open problem; this theorem is a
Lean-checked *reduction* of that question.  It states that the set of repunit primes is
infinite if and only if there are infinitely many *prime* exponents `p` for which the
repunit `repunit p = (10 ^ p - 1) / 9` is prime.  In particular one never has to look at
composite exponents: the two formulations of the conjecture are equivalent.
-/
