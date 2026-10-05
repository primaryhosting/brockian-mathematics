/-
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Finset

namespace Math

/-- A primitive 6-th root of unity `ζ` satisfies `ζ ^ 3 = -1`. -/
lemma cube_eq_neg_one {ζ : ℂ} (h : IsPrimitiveRoot ζ 6) : ζ ^ 3 = -1 := by
  have h6 : ζ ^ 6 = 1 := h.pow_eq_one
  have h3 : ζ ^ 3 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hsq : (ζ ^ 3) ^ 2 = 1 := by
    rw [← pow_mul]; simpa using h6
  rcases mul_self_eq_one_iff.1 (by linear_combination hsq : ζ ^ 3 * ζ ^ 3 = 1) with h' | h'
  · exact absurd h' h3
  · exact h'

/-- A primitive 6-th root of unity `ζ` satisfies `ζ ^ 2 - ζ + 1 = 0`. -/
lemma quad_eq_zero {ζ : ℂ} (h : IsPrimitiveRoot ζ 6) : ζ ^ 2 - ζ + 1 = 0 := by
  have h3 : ζ ^ 3 = -1 := cube_eq_neg_one h
  have hne : ζ + 1 ≠ 0 := by
    intro hc
    have hz : ζ = -1 := by linear_combination hc
    have h2 : ζ ^ 2 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    exact h2 (by rw [hz]; ring)
  have hfac : (ζ + 1) * (ζ ^ 2 - ζ + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.1 hfac with h' | h'
  · exact absurd h' hne
  · exact h'

/-- `μ(6) = 1`. -/
lemma moebius_six : (ArithmeticFunction.moebius 6 : ℤ) = 1 := by
  have h : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num)]
  norm_num

/-- The sum of the primitive 6-th roots of unity in `ℂ` equals `μ(6)`. -/
theorem mobius_root_sum_6 :
    ∑ z ∈ primitiveRoots 6 ℂ, z = ((ArithmeticFunction.moebius 6 : ℤ) : ℂ) := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 6)
  have hz : IsPrimitiveRoot ζ 6 := Complex.isPrimitiveRoot_exp 6 (by norm_num)
  have hz5 : IsPrimitiveRoot (ζ ^ 5) 6 := hz.pow_of_coprime 5 (by decide)
  have hzne0 : ζ ≠ 0 := hz.ne_zero (by norm_num)
  have hne : ζ ≠ ζ ^ 5 := by
    intro hc
    have h4 : ζ ^ 4 = 1 := by
      have : ζ * ζ ^ 4 = ζ * 1 := by linear_combination -hc
      exact mul_left_cancel₀ hzne0 this
    exact hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) h4
  have hsub : ({ζ, ζ ^ 5} : Finset ℂ) ⊆ primitiveRoots 6 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_primitiveRoots (by norm_num : 0 < 6)]
    rcases hx with rfl | rfl
    · exact hz
    · exact hz5
  have hcard : (primitiveRoots 6 ℂ).card ≤ ({ζ, ζ ^ 5} : Finset ℂ).card := by
    rw [Complex.card_primitiveRoots, Finset.card_insert_of_notMem (by simpa using hne),
      Finset.card_singleton]
    decide
  have hset : ({ζ, ζ ^ 5} : Finset ℂ) = primitiveRoots 6 ℂ :=
    Finset.eq_of_subset_of_card_le hsub hcard
  rw [← hset, Finset.sum_pair hne]
  have hq : ζ ^ 2 - ζ + 1 = 0 := quad_eq_zero hz
  have h3 : ζ ^ 3 = -1 := cube_eq_neg_one hz
  have : ζ + ζ ^ 5 = 1 := by linear_combination ζ ^ 2 * h3 - hq
  rw [this, moebius_six]
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

