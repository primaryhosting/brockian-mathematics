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

/-- The sum of the primitive 5-th roots of unity in `ℂ` equals `μ 5` (which is `-1`). -/
theorem mobius_root_sum_5 :
    ∑ z ∈ primitiveRoots 5 ℂ, z = (ArithmeticFunction.moebius 5 : ℂ) := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5) with hζdef
  have hζ : IsPrimitiveRoot ζ 5 := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  set T : Finset ℂ := (Finset.Ico 1 5).image (fun i => ζ ^ i) with hT
  have hinj : Set.InjOn (fun i => ζ ^ i) (Finset.Ico 1 5 : Finset ℕ) := by
    intro i hi j hj h
    simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
    exact hζ.pow_inj hi.2 hj.2 h
  have hsub : T ⊆ primitiveRoots 5 ℂ := by
    intro x hx
    simp only [hT, Finset.mem_image, Finset.mem_Ico] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [mem_primitiveRoots (by norm_num)]
    refine hζ.pow_of_coprime i ?_
    have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl|rfl|rfl|rfl <;> decide
  have hcardT : T.card = 4 := by
    rw [hT, Finset.card_image_of_injOn hinj]
    simp
  have hcardP : (primitiveRoots 5 ℂ).card = 4 := by
    rw [Complex.card_primitiveRoots]
    decide
  have heq : T = primitiveRoots 5 ℂ :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcardP, hcardT])
  rw [← heq, hT, Finset.sum_image hinj]
  have h0 : ∑ i ∈ Finset.range 5, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hIco : ∑ i ∈ Finset.Ico 1 5, ζ ^ i = -1 := by
    have hins : Finset.range 5 = insert 0 (Finset.Ico 1 5) := by decide +kernel
    rw [hins, Finset.sum_insert (by simp), pow_zero] at h0
    linear_combination h0
  rw [hIco, ArithmeticFunction.moebius_apply_prime (by norm_num)]
  norm_num

end Math
#print axioms Math.mobius_root_sum_5

