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

theorem clement_iff {n : ℕ} (hn : 3 ≤ n) :
    IsTwinPrime n ↔ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n :=
  ⟨clement_of_isTwinPrime hn, isTwinPrime_of_clement hn⟩

/-- A concrete instance of Clement's congruence: `5 * 7 ∣ 4 * (4! + 1) + 5 = 105`. -/
example : (5 : ℕ) * (5 + 2) ∣ 4 * ((5 - 1)! + 1) + 5 := by decide

/-- Every twin prime is at least `3`. -/
