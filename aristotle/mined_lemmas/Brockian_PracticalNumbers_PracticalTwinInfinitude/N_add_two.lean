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

lemma N_add_two (i : ℕ) : N i + 2 = 2 * 2 ^ (2 ^ i) := by
  induction i with
  | zero => norm_num [N]
  | succ i ih =>
      have hsq : (2:ℕ) ^ (2 ^ (i + 1)) = 2 ^ (2 ^ i) * 2 ^ (2 ^ i) := by
        rw [← pow_add]
        congr 1
        ring
      have hN : N (i + 1) = N i * (2 ^ (2 ^ i) + 1) := rfl
      rw [hN, hsq]
      nlinarith [ih]

