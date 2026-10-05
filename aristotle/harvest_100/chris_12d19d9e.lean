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

/-- The primitive 4-th roots of unity in `ℂ` are exactly `I` and `-I`. -/
theorem primitiveRoots_four_complex : primitiveRoots 4 ℂ = {Complex.I, -Complex.I} := by
  ext x
  rw [mem_primitiveRoots (by norm_num), Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have h4 : x ^ 4 = 1 := h.pow_eq_one
    have h2 : x ^ 2 ≠ 1 := fun hx => by simpa using h.dvd_of_pow_eq_one 2 hx
    have key : (x - Complex.I) * (x + Complex.I) = 0 := by
      have hfac : (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by linear_combination h4
      rcases mul_eq_zero.1 hfac with h' | h'
      · exact absurd (by linear_combination h') h2
      · linear_combination h' - Complex.I_sq
    rcases mul_eq_zero.1 key with h' | h'
    · exact Or.inl (by linear_combination h')
    · exact Or.inr (by linear_combination h')
  · rintro (rfl | rfl) <;> rw [IsPrimitiveRoot.iff (by norm_num)] <;>
      refine ⟨by simp [pow_succ, Complex.I_mul_I], ?_⟩ <;>
      · intro l hl hl0
        interval_cases l <;> simp [pow_succ, Complex.I_mul_I] <;> norm_num [Complex.ext_iff]

/-- The sum of the primitive 4-th roots of unity equals `μ 4` (which is `0`, since `4 = 2 ^ 2`
is not squarefree). -/
theorem mobius_root_sum_4 :
    ∑ z ∈ primitiveRoots 4 ℂ, z = (ArithmeticFunction.moebius 4 : ℂ) := by
  have hne : (Complex.I : ℂ) ≠ -Complex.I := by
    simp [Complex.ext_iff, (by norm_num : ¬(1 : ℝ) = -1)]
  have hmu : (ArithmeticFunction.moebius 4 : ℤ) = 0 := by decide
  rw [primitiveRoots_four_complex, Finset.sum_pair hne, hmu]
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

