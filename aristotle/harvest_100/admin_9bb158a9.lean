/-
# Mobius Root Sum 7
Category: Pure Mathematics
Target: Math.mobius_root_sum_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 7
Category: Pure Mathematics
Target: Math.mobius_root_sum_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- The primitive 7-th roots of unity in `ℂ` are exactly the powers `ζ ^ i`, `1 ≤ i < 7`,
where `ζ = exp (2 π i / 7)`; hence their sum is `-1`. -/
theorem sum_primitiveRoots_seven : ∑ z ∈ primitiveRoots 7 ℂ, z = -1 := by
  have h7 : (0 : ℕ) < 7 := by norm_num
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7) with hζdef
  have hζ : IsPrimitiveRoot ζ 7 := Complex.isPrimitiveRoot_exp 7 (by norm_num)
  have key : ∑ z ∈ primitiveRoots 7 ℂ, z = ∑ i ∈ Finset.Ico 1 7, ζ ^ i := by
    refine (Finset.sum_bij (fun i _ => ζ ^ i) ?_ ?_ ?_ ?_).symm
    · intro i hi
      simp only [Finset.mem_Ico] at hi
      rw [mem_primitiveRoots h7]
      refine hζ.pow_of_coprime i ?_
      exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr
        (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) |>.symm
    · intro i hi j hj H
      simp only [Finset.mem_Ico] at hi hj
      exact hζ.pow_inj (by omega) (by omega) H
    · intro b hb
      rw [mem_primitiveRoots h7, hζ.isPrimitiveRoot_iff] at hb
      obtain ⟨i, hin, hi, H⟩ := hb
      refine ⟨i, ?_, H⟩
      simp only [Finset.mem_Ico]
      refine ⟨?_, hin⟩
      rcases Nat.eq_zero_or_pos i with rfl | h
      · simp [Nat.coprime_zero_left] at hi
      · exact h
    · intro i hi; rfl
  rw [key]
  have hgeom : ∑ i ∈ Finset.range 7, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hsplit : ∑ i ∈ Finset.range 7, ζ ^ i = 1 + ∑ i ∈ Finset.Ico 1 7, ζ ^ i := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by norm_num)]
    simp
  rw [hgeom] at hsplit
  linear_combination -hsplit

/-- **Möbius root sum for 7.** The sum of the primitive 7-th roots of unity equals `μ 7`. -/
theorem mobius_root_sum_7 :
    ∑ z ∈ primitiveRoots 7 ℂ, z = ((ArithmeticFunction.moebius 7 : ℤ) : ℂ) := by
  rw [sum_primitiveRoots_seven, ArithmeticFunction.moebius_apply_prime (by norm_num)]
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

