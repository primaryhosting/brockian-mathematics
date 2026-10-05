import Mathlib

/-!
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- A primitive `6`-th root of unity `ζ` in `ℂ` satisfies `ζ ^ 3 = -1`. -/
theorem cube_eq_neg_one_of_isPrimitiveRoot_six {ζ : ℂ} (h : IsPrimitiveRoot ζ 6) :
    ζ ^ 3 = -1 := by
  have h6 : ζ ^ 6 = 1 := h.pow_eq_one
  have h3 : ζ ^ 3 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have key : (ζ ^ 3 - 1) * (ζ ^ 3 + 1) = 0 := by linear_combination h6
  rcases mul_eq_zero.1 key with h' | h'
  · exact absurd (by linear_combination h' : ζ ^ 3 = 1) h3
  · linear_combination h'

/-- A primitive `6`-th root of unity `ζ` in `ℂ` satisfies `ζ ^ 2 - ζ + 1 = 0`. -/
theorem sq_sub_self_add_one_of_isPrimitiveRoot_six {ζ : ℂ} (h : IsPrimitiveRoot ζ 6) :
    ζ ^ 2 - ζ + 1 = 0 := by
  have h2 : ζ ^ 2 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hcube : ζ ^ 3 = -1 := cube_eq_neg_one_of_isPrimitiveRoot_six h
  have hne : ζ + 1 ≠ 0 := by
    intro h'
    exact h2 (by linear_combination (ζ - 1) * h')
  have key : (ζ + 1) * (ζ ^ 2 - ζ + 1) = 0 := by linear_combination hcube
  rcases mul_eq_zero.1 key with h' | h'
  · exact absurd h' hne
  · exact h'

/-- A primitive `6`-th root of unity is different from its fifth power. -/
theorem ne_pow_five_of_isPrimitiveRoot_six {ζ : ℂ} (h : IsPrimitiveRoot ζ 6) :
    ζ ≠ ζ ^ 5 := by
  intro he
  have hζ0 : ζ ≠ 0 := h.ne_zero (by norm_num)
  have h4 : ζ ^ 4 = 1 := by
    have : ζ * (ζ ^ 4 - 1) = 0 := by linear_combination -he
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hζ0
    · linear_combination h'
  exact h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) h4

/-- The set of primitive `6`-th roots of unity in `ℂ` is `{ζ, ζ ^ 5}` for any
primitive `6`-th root of unity `ζ`. -/
theorem primitiveRoots_six_eq {ζ : ℂ} (h : IsPrimitiveRoot ζ 6) :
    primitiveRoots 6 ℂ = {ζ, ζ ^ 5} := by
  have hne : ζ ≠ ζ ^ 5 := ne_pow_five_of_isPrimitiveRoot_six h
  have hsub : ({ζ, ζ ^ 5} : Finset ℂ) ⊆ primitiveRoots 6 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_primitiveRoots (by norm_num : 0 < 6)]
    rcases hx with rfl | rfl
    · exact h
    · exact h.pow_of_coprime 5 (by norm_num)
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [Complex.card_primitiveRoots,
    Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  decide

/-- The sum of the primitive `6`-th roots of unity equals `μ 6`. -/
theorem mobius_root_sum_6 :
    ∑ z ∈ primitiveRoots 6 ℂ, z = (ArithmeticFunction.moebius 6 : ℂ) := by
  have h : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 6)) 6 :=
    Complex.isPrimitiveRoot_exp 6 (by norm_num)
  set ζ := Complex.exp (2 * Real.pi * Complex.I / 6) with hζdef
  have hne : ζ ≠ ζ ^ 5 := ne_pow_five_of_isPrimitiveRoot_six h
  rw [primitiveRoots_six_eq h, Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  have hq := sq_sub_self_add_one_of_isPrimitiveRoot_six h
  have hcube := cube_eq_neg_one_of_isPrimitiveRoot_six h
  have hmu : (ArithmeticFunction.moebius 6 : ℂ) = 1 := by
    have h6 : (6 : ℕ) = 2 * 3 := by norm_num
    have : ArithmeticFunction.moebius 6 = 1 := by
      rw [h6, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
        ArithmeticFunction.moebius_apply_prime (by norm_num),
        ArithmeticFunction.moebius_apply_prime (by norm_num)]
      norm_num
    rw [this]; norm_num
  rw [hmu]
  linear_combination (ζ ^ 2) * hcube - hq

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

