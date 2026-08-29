/-!
# Mobius Root Sum 7
Category: Pure Mathematics
Target: Math.mobius_root_sum_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset Polynomial

namespace Math

/-- The set of primitive `7`-th roots of unity in `ℂ` is the image of `{1, …, 6}` under
`i ↦ ζ ^ i`, where `ζ` is any primitive `7`-th root of unity. -/
lemma primitiveRoots_seven_eq_image {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 7) :
    primitiveRoots 7 ℂ = (Finset.Ico 1 7).image (fun i => ζ ^ i) := by
  ext x
  simp only [mem_primitiveRoots (by norm_num : (0:ℕ) < 7), Finset.mem_image, Finset.mem_Ico]
  constructor
  · intro hx
    obtain ⟨i, hi7, _, rfl⟩ := (hζ.isPrimitiveRoot_iff (by norm_num)).1 hx
    refine ⟨i, ⟨?_, hi7⟩, rfl⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp at hx
    · exact hpos
  · rintro ⟨i, ⟨hi1, hi7⟩, rfl⟩
    have hco : Nat.Coprime i 7 := by interval_cases i <;> decide
    exact hζ.pow_of_coprime i hco

/-- The sum of the primitive `7`-th roots of unity in `ℂ` equals `-1`. -/
lemma sum_primitiveRoots_seven : ∑ x ∈ primitiveRoots 7 ℂ, x = -1 := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7) with hζdef
  have hζ : IsPrimitiveRoot ζ 7 := Complex.isPrimitiveRoot_exp 7 (by norm_num)
  rw [primitiveRoots_seven_eq_image hζ, Finset.sum_image]
  · have hgeom : ∑ i ∈ Finset.range 7, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by norm_num : (0:ℕ) < 7)] at hgeom
    simp only [pow_zero] at hgeom
    linear_combination hgeom
  · intro i hi j hj hij
    simp only [Finset.mem_Ico] at hi hj
    exact hζ.pow_inj hi.2 hj.2 hij

/-- The sum of the primitive 7-th roots of unity equals `μ(7)`. -/
theorem mobius_root_sum_7 :
    ∑ x ∈ primitiveRoots 7 ℂ, x = (ArithmeticFunction.moebius 7 : ℂ) := by
  rw [sum_primitiveRoots_seven,
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7)]
  norm_num

end Math

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

