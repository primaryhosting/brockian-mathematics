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

open scoped BigOperators

namespace Brockian
namespace RepunitPrimes

/-- The `n`-th repunit `R n = 1 + 10 + ⋯ + 10 ^ (n - 1) = (10 ^ n - 1) / 9`,
i.e. the number written with `n` ones in base ten. -/

theorem repunitPrimeDivisorSet_infinite : repunitPrimeDivisorSet.Infinite := by
  have hsub : {p : ℕ | Nat.Prime p} \ ({2, 5} : Set ℕ) ⊆ repunitPrimeDivisorSet := by
    rintro p ⟨hp, hne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    exact ⟨hp, exists_repunit_dvd_of_prime hp hne.1 hne.2⟩
  exact Set.Infinite.mono hsub
    (Set.Infinite.diff Nat.infinite_setOf_prime (Set.toFinite _))

/-- **Conditional reduction for the infinitude of repunit primes.**

If for every bound `N` there is an index `n > N` with `R n` prime, then the set of
repunit primes is infinite.  (The hypothesis is the "unbounded index" form of the
conjecture; the conclusion is its "infinite set" form, and the reduction uses the
strict monotonicity of `n ↦ R n`.) -/
