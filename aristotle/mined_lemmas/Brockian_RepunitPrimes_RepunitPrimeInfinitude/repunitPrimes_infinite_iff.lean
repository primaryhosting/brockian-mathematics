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

theorem repunitPrimes_infinite_iff :
    repunitPrimes.Infinite ↔ ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (repunit n) := by
  constructor
  · intro hinf N
    obtain ⟨p, ⟨hp, n, rfl⟩, hlt⟩ := hinf.exists_gt (repunit N)
    exact ⟨n, repunit_strictMono.lt_iff_lt.mp hlt, hp⟩
  · exact RepunitPrimeInfinitude

/-- **Partial result (unconditional).** The index set of repunit primes consists of primes,
so the conjecture reduces to a statement about prime indices only. -/
