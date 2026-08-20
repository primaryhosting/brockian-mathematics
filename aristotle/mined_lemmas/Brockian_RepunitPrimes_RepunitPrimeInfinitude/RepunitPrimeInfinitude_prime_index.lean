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

theorem RepunitPrimeInfinitude_prime_index :
    (∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime (repunit n)) ↔
      (∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime n ∧ Nat.Prime (repunit n)) := by
  constructor
  · intro H N
    obtain ⟨n, hn, hprime⟩ := H N
    exact ⟨n, hn, prime_index_of_repunit_prime hprime, hprime⟩
  · intro H N
    obtain ⟨n, hn, _, hprime⟩ := H N
    exact ⟨n, hn, hprime⟩

end Brockian.RepunitPrimes


