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
# Mobius Root Sum 5
Category: Pure Mathematics
Target: Math.mobius_root_sum_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- The primitive 5-th roots of unity in `ℂ` are exactly `ζ, ζ², ζ³, ζ⁴`
for any fixed primitive 5-th root `ζ`. -/
theorem primitiveRoots_five_eq_image {ζ : ℂ} (h : IsPrimitiveRoot ζ 5) :
    primitiveRoots 5 ℂ = (Finset.Icc 1 4).image (fun i => ζ ^ i) := by
  ext z
  simp only [mem_primitiveRoots (by norm_num : (0 : ℕ) < 5), Finset.mem_image, Finset.mem_Icc]
  constructor
  · intro hz
    obtain ⟨i, hi, rfl⟩ := h.eq_pow_of_pow_eq_one hz.pow_eq_one
    refine ⟨i, ⟨?_, by omega⟩, rfl⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp only [pow_zero] at hz
      exact absurd (IsPrimitiveRoot.unique hz IsPrimitiveRoot.one) (by norm_num)
    · exact hpos
  · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
    exact h.pow_of_coprime i (by interval_cases i <;> decide)

/-- For a primitive 5-th root of unity `ζ`, we have `ζ + ζ² + ζ³ + ζ⁴ = -1`. -/
theorem sum_pow_primitive_five {ζ : ℂ} (h : IsPrimitiveRoot ζ 5) :
    ∑ i ∈ Finset.Icc 1 4, ζ ^ i = -1 := by
  have h5 : ζ ^ 5 = 1 := h.pow_eq_one
  have hne : ζ - 1 ≠ 0 := sub_ne_zero.mpr (fun hc => by
    rw [hc] at h; exact absurd (IsPrimitiveRoot.unique h IsPrimitiveRoot.one) (by norm_num))
  have hexp : ∑ i ∈ Finset.Icc 1 4, ζ ^ i = ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 := by
    simp [Finset.sum_Icc_succ_top]
  have key : (ζ - 1) * (∑ i ∈ Finset.Icc 1 4, ζ ^ i - -1) = 0 := by
    rw [hexp]; linear_combination h5
  have := (mul_eq_zero.mp key).resolve_left hne
  linear_combination this

/-- The sum of the primitive 5-th roots of unity equals `μ(5) = -1`. -/
theorem mobius_root_sum_5 :
    ∑ z ∈ primitiveRoots 5 ℂ, z = ((ArithmeticFunction.moebius 5 : ℤ) : ℂ) := by
  have h : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 5)) 5 :=
    Complex.isPrimitiveRoot_exp 5 (by norm_num)
  set ζ := Complex.exp (2 * Real.pi * Complex.I / 5)
  rw [primitiveRoots_five_eq_image h, Finset.sum_image, sum_pow_primitive_five h,
    ArithmeticFunction.moebius_apply_prime (by norm_num)]
  · norm_num
  · intro i hi j hj hij
    simp only [Finset.coe_Icc, Set.mem_Icc] at hi hj
    exact h.pow_inj (by omega) (by omega) hij

end Math

