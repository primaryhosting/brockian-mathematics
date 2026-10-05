/-
# Mobius Root Sum 4
Category: Pure Mathematics
Target: Math.mobius_root_sum_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- The primitive 4-th roots of unity in `ℂ` are exactly `I` and `-I`. -/
theorem primitiveRoots_four_complex : primitiveRoots 4 ℂ = {Complex.I, -Complex.I} := by
  ext z
  rw [mem_primitiveRoots (by norm_num), Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have h4 : z ^ 4 = 1 := h.pow_eq_one
    have h2 : z ^ 2 ≠ 1 := fun hz => by
      have := h.dvd_of_pow_eq_one 2 hz
      omega
    have key : (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.1 key with h' | h'
    · exact absurd (by linear_combination h') h2
    · have hfac : (z - Complex.I) * (z + Complex.I) = 0 := by
        linear_combination h' - Complex.I_sq
      rcases mul_eq_zero.1 hfac with h'' | h''
      · exact Or.inl (sub_eq_zero.1 h'')
      · exact Or.inr (eq_neg_of_add_eq_zero_left h'')
  · rintro (rfl | rfl) <;>
    · refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) (by simp [pow_succ, Complex.I_mul_I]) ?_
      intro l hl hlt
      interval_cases l <;> norm_num [pow_succ, Complex.I_mul_I, Complex.ext_iff]

/-- The sum of the primitive 4-th roots of unity equals `μ(4)` (both are `0`). -/
theorem mobius_root_sum_4 :
    ∑ z ∈ primitiveRoots 4 ℂ, z = ((ArithmeticFunction.moebius 4 : ℤ) : ℂ) := by
  have hmu : (ArithmeticFunction.moebius 4 : ℤ) = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  rw [primitiveRoots_four_complex, hmu,
    Finset.sum_insert (by simp [Complex.ext_iff]; norm_num), Finset.sum_singleton]
  ring

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

