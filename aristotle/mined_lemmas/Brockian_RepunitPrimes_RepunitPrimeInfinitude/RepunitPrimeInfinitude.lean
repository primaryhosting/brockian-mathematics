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

open Finset

/-- The `n`-th base-ten repunit `1, 11, 111, ...` (with `repunit 0 = 0`). -/

theorem RepunitPrimeInfinitude :
    (∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime (repunit n)) ↔ RepunitPrimeSet.Infinite := by
  constructor
  · intro H
    refine Set.infinite_of_forall_exists_gt fun N => ?_
    obtain ⟨n, hn, hprime⟩ := H N
    exact ⟨repunit n, ⟨hprime, ⟨n, rfl⟩⟩, lt_of_lt_of_le hn (le_repunit n)⟩
  · intro H N
    obtain ⟨p, ⟨hp, n, rfl⟩, hlt⟩ := H.exists_gt (repunit N)
    exact ⟨n, repunit_strictMono.lt_iff_lt.mp hlt, hp⟩

/-- Every index of a repunit prime is itself prime, so the conjecture may equivalently be
stated over prime indices. -/
