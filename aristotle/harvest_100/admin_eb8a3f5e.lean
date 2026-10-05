/-
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- The Möbius function at `6` equals `1`. -/
theorem moebius_six : ArithmeticFunction.moebius 6 = 1 := by
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h6, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num)]
  norm_num

/-- A primitive `6`-th root of unity `ζ` satisfies `ζ + ζ ^ 5 = 1`. -/
theorem add_pow_five_of_isPrimitiveRoot_six {ζ : ℂ} (h : IsPrimitiveRoot ζ 6) :
    ζ + ζ ^ 5 = 1 := by
  have h6 : ζ ^ 6 = 1 := h.pow_eq_one
  have h3 : ζ ^ 3 = -1 := by
    have h1 : ζ ^ 3 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    have hfac : (ζ ^ 3 - 1) * (ζ ^ 3 + 1) = 0 := by linear_combination h6
    rcases mul_eq_zero.1 hfac with hc | hc
    · exact absurd (by linear_combination hc) h1
    · linear_combination hc
  have h2 : ζ ≠ -1 := by
    intro he
    exact h.pow_ne_one_of_pos_of_lt (l := 2) (by norm_num) (by norm_num) (by rw [he]; ring)
  have key : ζ ^ 2 - ζ + 1 = 0 := by
    have hfac : (ζ + 1) * (ζ ^ 2 - ζ + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.1 hfac with hc | hc
    · exact absurd (by linear_combination hc) h2
    · exact hc
  linear_combination -key + ζ ^ 2 * h3

/-- The sum of the primitive `6`-th roots of unity in `ℂ` equals `μ 6`. -/
theorem mobius_root_sum_6 :
    ∑ z ∈ primitiveRoots 6 ℂ, z = (ArithmeticFunction.moebius 6 : ℂ) := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 6) with hζdef
  have h : IsPrimitiveRoot ζ 6 := Complex.isPrimitiveRoot_exp 6 (by norm_num)
  have h5 : IsPrimitiveRoot (ζ ^ 5) 6 := h.pow_of_coprime 5 (by norm_num)
  have hne : ζ ≠ ζ ^ 5 := by
    intro he
    have hz : ζ ≠ 0 := h.ne_zero (by norm_num)
    have h4 : ζ ^ 4 = 1 := by
      have hcancel : ζ * ζ ^ 4 = ζ * 1 := by rw [mul_one]; linear_combination -he
      exact mul_left_cancel₀ hz hcancel
    exact h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) h4
  have hsub : ({ζ, ζ ^ 5} : Finset ℂ) ⊆ primitiveRoots 6 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_primitiveRoots (by norm_num)).2 h
    · exact (mem_primitiveRoots (by norm_num)).2 h5
  have hcard : (primitiveRoots 6 ℂ).card ≤ ({ζ, ζ ^ 5} : Finset ℂ).card := by
    rw [h.card_primitiveRoots, Finset.card_insert_of_notMem (by simpa using hne),
      Finset.card_singleton]
    decide
  have hset : primitiveRoots 6 ℂ = {ζ, ζ ^ 5} := (Finset.eq_of_subset_of_card_le hsub hcard).symm
  rw [hset, Finset.sum_insert (by simpa using hne), Finset.sum_singleton, moebius_six,
    add_pow_five_of_isPrimitiveRoot_six h]
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

