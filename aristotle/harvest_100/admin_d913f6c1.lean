import Mathlib

/-!
# Mobius Root Sum 4
Category: Pure Mathematics
Target: Math.mobius_root_sum_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open Finset Complex

namespace Math

/-- `Complex.I` is a primitive 4-th root of unity. -/
theorem isPrimitiveRoot_I : IsPrimitiveRoot Complex.I 4 := by
  rw [IsPrimitiveRoot.iff_def]
  refine ⟨by norm_num, ?_⟩
  intro l hl
  have hpow : Complex.I ^ (l % 4) = 1 := by
    conv_rhs => rw [← hl]
    rw [← Nat.div_add_mod l 4, pow_add, pow_mul]
    norm_num
  have hcases : l % 4 = 0 ∨ l % 4 = 1 ∨ l % 4 = 2 ∨ l % 4 = 3 := by omega
  rcases hcases with h | h | h | h
  · exact Nat.dvd_of_mod_eq_zero h
  all_goals
    exfalso
    rw [h] at hpow
    norm_num [pow_succ, Complex.I_mul_I, Complex.ext_iff] at hpow

/-- The primitive 4-th roots of unity in `ℂ` are exactly `I` and `-I`. -/
theorem primitiveRoots_four : primitiveRoots 4 ℂ = {Complex.I, -Complex.I} := by
  ext z
  rw [mem_primitiveRoots (by norm_num)]
  constructor
  · intro hz
    have h4 : z ^ 4 = 1 := hz.pow_eq_one
    have h2 : z ^ 2 ≠ 1 := by
      intro h
      have := hz.dvd_of_pow_eq_one 2 h
      omega
    have : (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by ring_nf; linear_combination h4
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by linear_combination h) h2
    · have : (z - Complex.I) * (z + Complex.I) = 0 := by
        linear_combination h - Complex.I_sq
      rcases mul_eq_zero.mp this with h | h
      · exact Finset.mem_insert.mpr (Or.inl (by linear_combination h))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (by linear_combination h)))
  · intro hz
    rcases Finset.mem_insert.mp hz with h | h
    · exact h ▸ isPrimitiveRoot_I
    · have : z = -Complex.I := by simpa using h
      rw [this]
      simpa using isPrimitiveRoot_I.pow_of_coprime 3 (by norm_num)

/-- The sum of the primitive 4-th roots of unity equals `μ(4) = 0`. -/
theorem mobius_root_sum_4 :
    ∑ z ∈ primitiveRoots 4 ℂ, z = (ArithmeticFunction.moebius 4 : ℂ) := by
  rw [primitiveRoots_four]
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

