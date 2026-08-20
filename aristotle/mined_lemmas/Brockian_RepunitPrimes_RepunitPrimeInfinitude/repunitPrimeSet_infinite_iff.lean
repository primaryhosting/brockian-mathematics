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

theorem repunitPrimeSet_infinite_iff :
    repunitPrimeSet.Infinite ↔ ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (repunit n) := by
  refine ⟨fun hinf N => ?_, RepunitPrimeInfinitude⟩
  obtain ⟨p, hp, hgt⟩ := hinf.exists_gt (repunit N)
  obtain ⟨hpp, n, rfl⟩ := hp
  exact ⟨n, repunit_strictMono.lt_iff_lt.mp hgt, hpp⟩

/-- `R 2 = 11` is a repunit prime, so the set of repunit primes is nonempty. -/
