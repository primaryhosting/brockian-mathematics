import Mathlib

open Finset Complex Polynomial

namespace Math

/-- The sum of the primitive 7-th roots of unity in `ℂ` is `-1`. -/
theorem sum_primitiveRoots_seven_eq_neg_one :
    ∑ z ∈ primitiveRoots 7 ℂ, z = -1 := by
  have h7 : (7 : ℕ) ≠ 0 := by norm_num
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7) with hζdef
  have hζ : IsPrimitiveRoot ζ 7 := by
    simpa [hζdef] using Complex.isPrimitiveRoot_exp 7 h7
  have hbij : ∑ z ∈ primitiveRoots 7 ℂ, z
      = ∑ i ∈ (range 7).filter (fun i => Nat.Coprime 7 i), ζ ^ i := by
    refine (Finset.sum_bij (fun i _ => ζ ^ i) ?_ ?_ ?_ ?_).symm
    · intro i hi
      simp only [mem_filter, mem_range] at hi
      rw [mem_primitiveRoots (by norm_num)]
      exact hζ.pow_of_coprime i hi.2.symm
    · intro i hi j hj H
      simp only [mem_filter, mem_range] at hi hj
      exact hζ.pow_inj hi.1 hj.1 H
    · intro w hw
      rw [mem_primitiveRoots (by norm_num), hζ.isPrimitiveRoot_iff] at hw
      obtain ⟨i, hin, hi, H⟩ := hw
      exact ⟨i, by simp only [mem_filter, mem_range]; exact ⟨hin, hi.symm⟩, H⟩
    · intro i _
      rfl
  have hfil : (range 7).filter (fun i => Nat.Coprime 7 i) = ({1, 2, 3, 4, 5, 6} : Finset ℕ) := by
    decide
  have hgeom : ∑ i ∈ range 7, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hrange : ∑ i ∈ range 7, ζ ^ i = 1 + ∑ i ∈ ({1, 2, 3, 4, 5, 6} : Finset ℕ), ζ ^ i := by
    simp [Finset.sum_range_succ, Finset.sum_insert, Finset.mem_insert]
    ring
  rw [hrange] at hgeom
  rw [hbij, hfil]
  linear_combination hgeom

/-- The sum of the primitive 7-th roots of unity equals `μ 7`. -/
theorem mobius_root_sum_7 :
    ∑ z ∈ primitiveRoots 7 ℂ, z = (ArithmeticFunction.moebius 7 : ℂ) := by
  rw [sum_primitiveRoots_seven_eq_neg_one,
    ArithmeticFunction.moebius_apply_prime (by norm_num)]
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

