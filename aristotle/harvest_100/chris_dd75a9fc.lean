/-
# Mobius Root Sum 4
Category: Pure Mathematics
Target: Math.mobius_root_sum_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mobius Root Sum 4
Category: Pure Mathematics
Target: Math.mobius_root_sum_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Finset

/-- The set of primitive `4`-th roots of unity in `ℂ` is `{I, -I}`. -/
theorem primitiveRoots_four_complex :
    primitiveRoots 4 ℂ = {Complex.I, -Complex.I} := by
  ext x
  rw [mem_primitiveRoots (by norm_num), IsPrimitiveRoot.iff (by norm_num)]
  constructor
  · rintro ⟨h4, hlt⟩
    have h2 : x ^ 2 = -1 := by
      have : (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by ring_nf; linear_combination h4
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (by linear_combination h : x ^ 2 = 1) (hlt 2 (by norm_num) (by norm_num))
      · linear_combination h
    have : (x - Complex.I) * (x + Complex.I) = 0 := by
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination h2 - hI
    rcases mul_eq_zero.1 this with h | h
    · simp [sub_eq_zero.1 h]
    · simp [eq_neg_of_add_eq_zero_left h]
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    rcases hx with rfl | rfl
    · refine ⟨by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hI]; ring, ?_⟩
      intro l hl0 hl4
      interval_cases l <;> norm_num [pow_succ, Complex.ext_iff]
    · refine ⟨by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, neg_pow, hI]; ring, ?_⟩
      intro l hl0 hl4
      interval_cases l <;> norm_num [pow_succ, Complex.ext_iff]

/-- The sum of the primitive `4`-th roots of unity in `ℂ` equals `μ(4) = 0`. -/
theorem mobius_root_sum_4 :
    ∑ z ∈ primitiveRoots 4 ℂ, z = (ArithmeticFunction.moebius 4 : ℂ) := by
  rw [primitiveRoots_four_complex]
  rw [Finset.sum_insert (by norm_num [Complex.ext_iff]), Finset.sum_singleton]
  have : ArithmeticFunction.moebius 4 = 0 := by decide
  rw [this]
  simp

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

