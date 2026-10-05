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

open scoped Nat

namespace Brockian.TwinPrimes

/-- **The Twin Prime Conjecture**: there are arbitrarily large primes `p` such that
`p + 2` is also prime. -/

theorem twinPrimeConjecture_iff_clement :
    TwinPrimeConjecture ↔ ∀ N : ℕ, ∃ n : ℕ, N < n ∧ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n := by
  constructor
  · intro h N
    obtain ⟨p, hp, hp1, hp2⟩ := h N
    exact ⟨p, hp, (clement_criterion hp1.one_lt).mp ⟨hp1, hp2⟩⟩
  · intro h N
    obtain ⟨n, hn, hd⟩ := h (max N 1)
    have hn1 : 1 < n := lt_of_le_of_lt (le_max_right N 1) hn
    obtain ⟨hp, hq⟩ := (clement_criterion hn1).mpr hd
    exact ⟨n, lt_of_le_of_lt (le_max_left N 1) hn, hp, hq⟩

/-! ## An unconditional partial result -/

/-- Every twin prime pair beyond `(3,5)` has its smaller member congruent to `5` mod `6`. -/
