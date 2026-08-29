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

namespace Math

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- If `z` is a primitive 12-th root of unity in `ℂ`, then `z ^ 6 = -1`. -/

lemma neg_mem_primitiveRoots_twelve {z : ℂ} (hz : z ∈ primitiveRoots 12 ℂ) :
    -z ∈ primitiveRoots 12 ℂ := by
  have h : IsPrimitiveRoot z 12 := (mem_primitiveRoots (by norm_num)).mp hz
  have h6 : z ^ 6 = -1 := pow_six_eq_neg_one_of_isPrimitiveRoot_twelve h
  have h7 : z ^ 7 = -z := by
    have : z ^ 7 = z ^ 6 * z := by ring
    rw [this, h6]; ring
  have hcop : Nat.Coprime 7 12 := by decide
  have := h.pow_of_coprime 7 hcop
  rw [h7] at this
  exact (mem_primitiveRoots (by norm_num)).mpr this

/-- There are exactly four primitive 12-th roots of unity in `ℂ`. -/
