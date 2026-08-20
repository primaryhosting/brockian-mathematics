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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BrocardGap

/-- The number of primes strictly between `a` and `b`. -/

theorem succ_nth_prime_ge {n : ℕ} (hn : 1 ≤ n) :
    Nat.nth Nat.Prime n + 2 ≤ Nat.nth Nat.Prime (n + 1) := by
  have h3 : 3 ≤ Nat.nth Nat.Prime n := three_le_nth_prime hn
  have hlt : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
    (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 (Nat.lt_succ_self n)
  have hodd : Odd (Nat.nth Nat.Prime n) :=
    (Nat.prime_nth_prime n).odd_of_ne_two (by omega)
  have hodd' : Odd (Nat.nth Nat.Prime (n + 1)) :=
    (Nat.prime_nth_prime (n + 1)).odd_of_ne_two (by omega)
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨l, hl⟩ := hodd'
  omega

/-- **Brocard's gap conjecture**, conditional on Oppermann's conjecture: for `n ≥ 1`
(i.e. from the prime `3` on) there are at least four primes strictly between the squares
of two consecutive primes `p_n` and `p_{n+1}`. -/
