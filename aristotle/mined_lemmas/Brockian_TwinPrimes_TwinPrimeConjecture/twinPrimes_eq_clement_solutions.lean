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

theorem twinPrimes_eq_clement_solutions :
    twinPrimes = {n : ℕ | 3 ≤ n ∧ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n} := by
  ext n
  constructor
  · intro hn
    have h3 := three_le_of_isTwinPrime hn
    exact ⟨h3, clement_of_isTwinPrime h3 hn⟩
  · rintro ⟨h3, hd⟩
    exact isTwinPrime_of_clement h3 hd

/-- **Reduction of the twin prime conjecture to an elementary divisibility statement.**
There are infinitely many twin primes if and only if Clement's congruence
`n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n` has arbitrarily large solutions `n ≥ 3`. -/
