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
lemma moebius_six : (ArithmeticFunction.moebius 6 : ℤ) = 1 := by
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h6, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.moebius_apply_prime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num)]
  norm_num

/-- The set of primitive `6`-th roots of unity in `ℂ` consists of `ζ` and `ζ ^ 5`, where
`ζ = exp (2 π i / 6)`. -/
lemma primitiveRoots_six_eq :
    primitiveRoots 6 ℂ = {Complex.exp (2 * Real.pi * Complex.I / 6),
      Complex.exp (2 * Real.pi * Complex.I / 6) ^ 5} := by
  have h := Complex.isPrimitiveRoot_exp 6 (by norm_num)
  set z := Complex.exp (2 * Real.pi * Complex.I / 6) with hz
  have key : ∀ k : ℕ, z ^ k = 1 ↔ 6 ∣ k := fun k => h.pow_eq_one_iff_dvd k
  have h4 : z ^ 4 ≠ 1 := fun hc => by have := (key 4).1 hc; omega
  have hz5 : IsPrimitiveRoot (z ^ 5) 6 := h.pow_of_coprime 5 (by norm_num)
  have hne : z ≠ z ^ 5 := by
    intro hc
    refine h4 ?_
    have hz0 : z ≠ 0 := h.ne_zero (by norm_num)
    have : z * z ^ 4 = z * 1 := by rw [mul_one]; linear_combination -hc
    exact mul_left_cancel₀ hz0 this
  have hsub : ({z, z ^ 5} : Finset ℂ) ⊆ primitiveRoots 6 ℂ := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact (mem_primitiveRoots (by norm_num)).2 h
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact (mem_primitiveRoots (by norm_num)).2 hz5
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [h.card_primitiveRoots, Finset.card_insert_of_notMem (by simpa using hne),
    Finset.card_singleton]
  decide

/-- The sum of the primitive `6`-th roots of unity equals `μ(6)`. -/
theorem mobius_root_sum_6 :
    ∑ z ∈ primitiveRoots 6 ℂ, z = (ArithmeticFunction.moebius 6 : ℂ) := by
  have h := Complex.isPrimitiveRoot_exp 6 (by norm_num)
  set z := Complex.exp (2 * Real.pi * Complex.I / 6) with hz
  have key : ∀ k : ℕ, z ^ k = 1 ↔ 6 ∣ k := fun k => h.pow_eq_one_iff_dvd k
  have h6 : z ^ 6 = 1 := (key 6).2 (by norm_num)
  have h3 : z ^ 3 ≠ 1 := fun hc => by have := (key 3).1 hc; omega
  have h2 : z ^ 2 ≠ 1 := fun hc => by have := (key 2).1 hc; omega
  have h4 : z ^ 4 ≠ 1 := fun hc => by have := (key 4).1 hc; omega
  have hcube : z ^ 3 = -1 := by
    have hf : (z ^ 3 - 1) * (z ^ 3 + 1) = 0 := by linear_combination h6
    rcases mul_eq_zero.1 hf with h' | h'
    · exact absurd (by linear_combination h' : z ^ 3 = 1) h3
    · linear_combination h'
  have hq : z ^ 2 - z + 1 = 0 := by
    have hne : z + 1 ≠ 0 := fun hc => h2 (by linear_combination (z - 1) * hc)
    have hf : (z + 1) * (z ^ 2 - z + 1) = 0 := by linear_combination hcube
    exact (mul_eq_zero.1 hf).resolve_left hne
  have hne : z ≠ z ^ 5 := by
    intro hc
    refine h4 ?_
    have hz0 : z ≠ 0 := h.ne_zero (by norm_num)
    have : z * z ^ 4 = z * 1 := by rw [mul_one]; linear_combination -hc
    exact mul_left_cancel₀ hz0 this
  rw [primitiveRoots_six_eq, Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  rw [show ((ArithmeticFunction.moebius 6 : ℤ) : ℂ) = ((1 : ℤ) : ℂ) by rw [moebius_six]]
  push_cast
  linear_combination z ^ 2 * hcube - hq

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

