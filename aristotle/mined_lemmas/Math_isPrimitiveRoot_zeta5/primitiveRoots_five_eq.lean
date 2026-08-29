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
/-!
# Mobius Root Sum 5
Category: Pure Mathematics
Target: Math.mobius_root_sum_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open Finset Complex

namespace Math

/-- A fixed primitive 5-th root of unity in `ℂ`. -/

theorem primitiveRoots_five_eq :
    primitiveRoots 5 ℂ = (Finset.Ico 1 5).image (fun i => zeta5 ^ i) := by
  ext x
  simp only [mem_primitiveRoots (by norm_num : (0:ℕ) < 5), Finset.mem_image, Finset.mem_Ico]
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := isPrimitiveRoot_zeta5.eq_pow_of_pow_eq_one hx.pow_eq_one
    refine ⟨i, ⟨?_, hi⟩, hix⟩
    rcases Nat.eq_zero_or_pos i with h | h
    · exact absurd (by rw [← hix, h, pow_zero]) (hx.ne_one (by norm_num))
    · exact h
  · rintro ⟨i, ⟨hi1, hi5⟩, rfl⟩
    refine isPrimitiveRoot_zeta5.pow_of_coprime i ?_
    interval_cases i <;> decide

/-- The sum of the primitive 5-th roots of unity equals `μ 5`. -/
