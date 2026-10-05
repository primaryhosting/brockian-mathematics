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
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.TwinPrimes

open Nat

/-- `p` is a twin prime (the smaller member of a twin prime pair) if both `p` and `p + 2`
are prime. -/

theorem twinPrimes_infinite_iff_clement :
    twinPrimes.Infinite ↔
      ∀ N : ℕ, ∃ n, N < n ∧ 3 ≤ n ∧ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n := by
  rw [twinPrimes_infinite_iff]
  constructor
  · intro h N
    obtain ⟨p, hlt, hp⟩ := h N
    have h3 := three_le_of_isTwinPrime hp
    exact ⟨p, hlt, h3, clement_of_isTwinPrime h3 hp⟩
  · intro h N
    obtain ⟨n, hlt, h3, hd⟩ := h N
    exact ⟨n, hlt, isTwinPrime_of_clement h3 hd⟩

/-- **Conditional reduction of the twin prime conjecture.**  If for every bound `N` there is some
`n > N` with `n ≥ 3` satisfying Clement's divisibility congruence
`n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n`, then there are infinitely many twin primes. -/
