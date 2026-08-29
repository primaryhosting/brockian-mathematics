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
noncomputable def zeta9 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9)

theorem isPrimitiveRoot_zeta9 : IsPrimitiveRoot zeta9 9 :=
  Complex.isPrimitiveRoot_exp 9 (by norm_num)

/-- The primitive 9-th roots of unity are exactly the powers `ζ^k` for
`k ∈ {1, 2, 4, 5, 7, 8}`. -/
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

theorem zeta9_cube_sum : 1 + zeta9 ^ 3 + zeta9 ^ 6 = 0 := by
  have h9 : zeta9 ^ 9 = 1 := isPrimitiveRoot_zeta9.pow_eq_one
  have hne : zeta9 ^ 3 - 1 ≠ 0 := fun h =>
    isPrimitiveRoot_zeta9.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) (sub_eq_zero.mp h)
  have key : (zeta9 ^ 3 - 1) * (1 + zeta9 ^ 3 + zeta9 ^ 6) = 0 := by
    linear_combination h9
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hne
  · exact h

/-- **The sum of the primitive 9-th roots of unity equals `μ(9)`.** -/
theorem mobius_root_sum_9 :
    ∑ z ∈ primitiveRoots 9 ℂ, z = (ArithmeticFunction.moebius 9 : ℂ) := by
  have hmu : ArithmeticFunction.moebius 9 = 0 := by
    refine ArithmeticFunction.moebius_eq_zero_of_not_squarefree ?_
    intro h
    have := h 3 (by norm_num)
    simp at this
  have hinj : Set.InjOn (fun k : ℕ => zeta9 ^ k) ({1, 2, 4, 5, 7, 8} : Finset ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at ha hb
    have ha9 : a < 9 := by rcases ha with h | h | h | h | h | h <;> omega
    have hb9 : b < 9 := by rcases hb with h | h | h | h | h | h <;> omega
    exact isPrimitiveRoot_zeta9.pow_inj ha9 hb9 hab
  rw [hmu, primitiveRoots_nine_eq, Finset.sum_image hinj]
  have h := zeta9_cube_sum
  push_cast
  norm_num [Finset.sum_insert, Finset.mem_insert]
  linear_combination (zeta9 + zeta9 ^ 2) * h

end Math

