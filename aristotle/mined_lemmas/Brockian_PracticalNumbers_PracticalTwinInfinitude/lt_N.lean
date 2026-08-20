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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

open Finset

/-- A natural number `n` is *practical* if it is positive and every `m ≤ n` can be written
as a sum of distinct divisors of `n`. -/

lemma lt_N (B : ℕ) : B < N B := by
  have h := N_add_two B
  have h2 := two_le_pow B
  have hB : B < 2 ^ B := Nat.lt_two_pow_self
  have hmono : (2:ℕ) ^ B ≤ 2 ^ (2 ^ B) := Nat.pow_le_pow_right (by norm_num) hB.le
  omega

/-- **Practical twin infinitude**: there are infinitely many `n` such that both `n` and `n + 2`
are practical numbers. -/
