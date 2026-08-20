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

lemma sum_union_image (hk : 0 < k)
    (hdisj : Disjoint D (D.image (fun d => k * d))) :
    ∑ x ∈ (D ∪ D.image (fun d => k * d)), x = (1 + k) * ∑ x ∈ D, x := by
  rw [Finset.sum_union hdisj,
    Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hk h), ← Finset.mul_sum]
  ring

/-- The key scaling step: if `D` is complete and `k ≤ (∑ D) + 1`, then `D ∪ k • D`
is complete (provided the two pieces are disjoint). -/
