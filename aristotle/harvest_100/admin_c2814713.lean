import Mathlib

open Finset

namespace Math

/-- Every primitive 8-th root of unity `ζ` in `ℂ` satisfies `ζ ^ 4 = -1`. -/
lemma pow_four_eq_neg_one_of_mem_primitiveRoots_eight
    {ζ : ℂ} (hζ : ζ ∈ primitiveRoots 8 ℂ) : ζ ^ 4 = -1 := by
  rw [mem_primitiveRoots (by norm_num)] at hζ
  have h8 : ζ ^ 8 = 1 := hζ.pow_eq_one
  have h4 : ζ ^ 4 ≠ 1 := by
    intro h
    have := (hζ.pow_eq_one_iff_dvd 4).1 h
    omega
  have hsq : (ζ ^ 4 - 1) * (ζ ^ 4 + 1) = 0 := by linear_combination h8
  rcases mul_eq_zero.1 hsq with h | h
  · exact absurd (sub_eq_zero.1 h) h4
  · linear_combination h

/-- The Möbius function vanishes at `8`, since `8 = 2 ^ 3` is not squarefree. -/
lemma moebius_eight : ArithmeticFunction.moebius 8 = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)

/-- **The sum of the primitive 8-th roots of unity equals `μ 8`** (both are `0`). -/
theorem mobius_root_sum_8 :
    ∑ ζ ∈ primitiveRoots 8 ℂ, ζ = (ArithmeticFunction.moebius 8 : ℂ) := by
  have hmem : ∀ ζ ∈ primitiveRoots 8 ℂ, ζ ^ 5 ∈ primitiveRoots 8 ℂ := by
    intro ζ hζ
    rw [mem_primitiveRoots (by norm_num)] at hζ ⊢
    exact hζ.pow_of_coprime 5 (by norm_num)
  have hinv : ∀ ζ ∈ primitiveRoots 8 ℂ, (ζ ^ 5) ^ 5 = ζ := by
    intro ζ hζ
    have h8 : ζ ^ 8 = 1 := by
      rw [mem_primitiveRoots (by norm_num)] at hζ
      exact hζ.pow_eq_one
    calc (ζ ^ 5) ^ 5 = (ζ ^ 8) ^ 3 * ζ := by ring
      _ = ζ := by rw [h8]; ring
  -- Raising to the 5-th power permutes the primitive 8-th roots of unity.
  have key : ∑ ζ ∈ primitiveRoots 8 ℂ, ζ = ∑ ζ ∈ primitiveRoots 8 ℂ, ζ ^ 5 :=
    Finset.sum_nbij' (fun ζ => ζ ^ 5) (fun ζ => ζ ^ 5) hmem hmem hinv hinv
      (fun a ha => (hinv a ha).symm)
  -- but `ζ ^ 5 = -ζ`, so the sum equals its own negative.
  have key2 : ∑ ζ ∈ primitiveRoots 8 ℂ, ζ ^ 5 = - ∑ ζ ∈ primitiveRoots 8 ℂ, ζ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ζ hζ => ?_
    have h4 := pow_four_eq_neg_one_of_mem_primitiveRoots_eight hζ
    calc ζ ^ 5 = ζ ^ 4 * ζ := by ring
      _ = -ζ := by rw [h4]; ring
  have hzero : ∑ ζ ∈ primitiveRoots 8 ℂ, ζ = 0 := by
    have h := key.trans key2
    linear_combination h / 2
  rw [hzero, moebius_eight]
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

