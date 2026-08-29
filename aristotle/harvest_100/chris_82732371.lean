/-
# Mobius Root Sum 2
Category: Pure Mathematics
Target: Math.mobius_root_sum_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- The set of primitive `2`-th roots of unity in `ℂ` is `{-1}`. -/
theorem primitiveRoots_two_complex : primitiveRoots 2 ℂ = {-1} := by
  ext z
  rw [mem_primitiveRoots (by norm_num)]
  simp only [IsPrimitiveRoot.iff_def, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    have hz1 : z ≠ 1 := by
      intro hz
      have := h2 1 (by simp [hz])
      omega
    have hfac : (z - 1) * (z + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (sub_eq_zero.1 h) hz1
    · exact eq_neg_of_add_eq_zero_left h
  · rintro rfl
    refine ⟨by norm_num, fun l hl => ?_⟩
    rcases Nat.even_or_odd l with he | ho
    · exact he.two_dvd
    · rw [ho.neg_one_pow] at hl
      norm_num at hl

/-- The sum of the primitive `2`-th roots of unity equals `μ(2) = -1`. -/
theorem mobius_root_sum_2 :
    ∑ z ∈ primitiveRoots 2 ℂ, z = (ArithmeticFunction.moebius 2 : ℤ) := by
  rw [primitiveRoots_two_complex]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two]

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

