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

lemma N_le_sum_Dset (i : ℕ) : N i ≤ ∑ x ∈ Dset i, x := by
  induction i with
  | zero => norm_num [N, Dset]
  | succ i ih =>
      show N (i + 1) ≤ ∑ x ∈ (Dset i ∪ (Dset i).image (fun d => F i * d)), x
      rw [sum_union_image (Dset i) (F i) (F_pos i) (Dset_disjoint i)]
      have hN : N (i + 1) = N i * F i := rfl
      rw [hN]
      calc N i * F i ≤ (∑ x ∈ Dset i, x) * F i := Nat.mul_le_mul_right _ ih
        _ ≤ (1 + F i) * ∑ x ∈ Dset i, x := by nlinarith [Nat.zero_le (∑ x ∈ Dset i, x)]

