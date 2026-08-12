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

open Finset

namespace Math

/-- A fixed primitive 5-th root of unity in `ℂ`. -/
noncomputable def zeta5 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

lemma isPrimitiveRoot_zeta5 : IsPrimitiveRoot Math.zeta5 5 := by
  simpa [Math.zeta5] using Complex.isPrimitiveRoot_exp 5 (by norm_num)

lemma zeta5_pow_injOn :
    Set.InjOn (fun i : ℕ => Math.zeta5 ^ i) (Finset.Ico 1 5 : Finset ℕ) := by
  intro i hi j hj hij
  simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
  exact Math.isPrimitiveRoot_zeta5.pow_inj hi.2 hj.2 hij

/-- The primitive 5-th roots of unity are exactly `ζ, ζ², ζ³, ζ⁴` for `ζ = exp(2πi/5)`. -/
lemma primitiveRoots_five_eq :
    primitiveRoots 5 ℂ = (Finset.Ico 1 5).image (fun i : ℕ => Math.zeta5 ^ i) := by
  have h := Math.isPrimitiveRoot_zeta5
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_Ico] at hx
    obtain ⟨i, ⟨hi1, hi2⟩, rfl⟩ := hx
    rw [mem_primitiveRoots (by norm_num)]
    refine h.pow_of_coprime i ?_
    have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> decide
  · rw [Complex.card_primitiveRoots, Finset.card_image_of_injOn Math.zeta5_pow_injOn,
      Nat.card_Ico]
    decide

/-- The sum of the primitive 5-th roots of unity equals the Möbius function `μ(5) = -1`. -/
theorem mobius_root_sum_5 :
    ∑ z ∈ primitiveRoots 5 ℂ, z = ((ArithmeticFunction.moebius 5 : ℤ) : ℂ) := by
  have h := Math.isPrimitiveRoot_zeta5
  have hz : ∑ i ∈ Finset.range 5, Math.zeta5 ^ i = 0 := h.geom_sum_eq_zero (by norm_num)
  have hr : Finset.range 5 = insert 0 (Finset.Ico 1 5) := by decide
  rw [hr, Finset.sum_insert (by simp)] at hz
  have h5 : (ArithmeticFunction.moebius 5 : ℤ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
  rw [Math.primitiveRoots_five_eq, Finset.sum_image (fun i hi j hj hij =>
      Math.zeta5_pow_injOn (by simpa using hi) (by simpa using hj) hij), h5]
  push_cast
  linear_combination hz

end Math

#print axioms Math.mobius_root_sum_5

