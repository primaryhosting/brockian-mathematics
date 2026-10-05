/-
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- For a primitive `11`-th root of unity `ζ` in `ℂ`, the set of primitive `11`-th roots of
unity is exactly `{ζ ^ 1, ..., ζ ^ 10}`. -/
lemma primitiveRoots_eleven_eq_image {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 11) :
    primitiveRoots 11 ℂ = (Finset.Ico 1 11).image (fun i => ζ ^ i) := by
  ext ξ
  simp only [Finset.mem_image, Finset.mem_Ico, mem_primitiveRoots (by norm_num : 0 < 11)]
  constructor
  · intro hξ
    obtain ⟨i, hi, hpow⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
    refine ⟨i, ⟨?_, hi⟩, hpow⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [pow_zero] at hpow
      subst hpow
      exact absurd (hξ.unique IsPrimitiveRoot.one) (by norm_num)
    · exact hpos
  · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
    refine hζ.pow_of_coprime i ?_
    interval_cases i <;> decide

/-- The sum of the primitive `11`-th roots of unity equals `μ(11)`. -/
theorem mobius_root_sum_11 :
    ∑ ζ ∈ primitiveRoots 11 ℂ, ζ = (ArithmeticFunction.moebius 11 : ℂ) := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 11)) 11 :=
    Complex.isPrimitiveRoot_exp 11 (by norm_num)
  set ζ := Complex.exp (2 * Real.pi * Complex.I / 11) with hζdef
  have hgeom : ∑ i ∈ Finset.range 11, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hsplit : ∑ i ∈ Finset.Ico 0 11, ζ ^ i = ζ ^ 0 + ∑ i ∈ Finset.Ico 1 11, ζ ^ i :=
    Finset.sum_eq_sum_Ico_succ_bot (by norm_num) _
  rw [Finset.range_eq_Ico] at hgeom
  rw [hsplit, pow_zero] at hgeom
  have hsum : ∑ i ∈ Finset.Ico 1 11, ζ ^ i = -1 := by linear_combination hgeom
  rw [primitiveRoots_eleven_eq_image hζ, Finset.sum_image (by
    intro i hi j hj hij
    simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
    exact hζ.pow_inj hi.2 hj.2 hij), hsum]
  rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
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

