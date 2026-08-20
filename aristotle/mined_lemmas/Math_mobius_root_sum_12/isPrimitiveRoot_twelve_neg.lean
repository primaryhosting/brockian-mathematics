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
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/



namespace Math

open Finset

/-- A primitive 12-th root of unity satisfies `z ^ 6 = -1`. -/

lemma isPrimitiveRoot_twelve_neg {z : ℂ} (h : IsPrimitiveRoot z 12) :
    IsPrimitiveRoot (-z) 12 := by
  have hz7 : -z = z ^ 7 := by
    have h6 := pow_six_eq_neg_one_of_isPrimitiveRoot_twelve h
    calc -z = z ^ 6 * z := by rw [h6]; ring
      _ = z ^ 7 := by ring
  rw [hz7]
  exact h.pow_of_coprime 7 (by decide)

/-- **The sum of the primitive 12-th roots of unity equals `μ(12)`.**

Both sides are `0`: `12 = 2 ^ 2 * 3` is not squarefree, so `μ(12) = 0`, while the primitive
12-th roots of unity come in pairs `{z, -z}` (since `-z = z ^ 7` is again primitive), so they
cancel in the sum. -/
