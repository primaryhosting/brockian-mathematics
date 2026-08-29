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

theorem not_twinPrimeConjecture_iff :
    ¬ TwinPrimeConjecture ↔ ∃ N : ℕ, ∀ p : ℕ, N < p → ¬ (p.Prime ∧ (p + 2).Prime) := by
  unfold TwinPrimeConjecture
  push_neg
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun p hp hpp => (hN p hp hpp.1) hpp.2⟩
  · rintro ⟨N, hN⟩
    exact ⟨N, fun p hp hpp hpp2 => hN p hp ⟨hpp, hpp2⟩⟩

/-! ## Wilson's theorem in divisibility form -/

/-- Wilson's theorem, stated with divisibility of natural numbers:
for `n > 1`, `n` is prime iff `n ∣ (n-1)! + 1`. -/
