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
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- A fixed primitive 9-th root of unity in `ℂ`. -/

theorem primitiveRoots_nine_eq :
    primitiveRoots 9 ℂ = ({1, 2, 4, 5, 7, 8} : Finset ℕ).image (fun k => zeta9 ^ k) := by
  ext x
  simp only [Finset.mem_image, mem_primitiveRoots (by norm_num : 0 < 9)]
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := isPrimitiveRoot_zeta9.eq_pow_of_pow_eq_one hx.pow_eq_one
    rw [isPrimitiveRoot_zeta9.pow_iff_coprime (by norm_num)] at hx
    refine ⟨i, ?_, rfl⟩
    interval_cases i <;> simp_all [Nat.Coprime]
  · rintro ⟨k, hk, rfl⟩
    rw [isPrimitiveRoot_zeta9.pow_iff_coprime (by norm_num)]
    fin_cases hk <;> decide

