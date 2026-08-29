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

open Finset Complex

/-- `Complex.I` is a primitive 4-th root of unity. -/

theorem primitiveRoots_four_eq : primitiveRoots 4 ℂ = {Complex.I, -Complex.I} := by
  ext z
  rw [mem_primitiveRoots (by norm_num)]
  constructor
  · intro hz
    have h4 : z ^ 4 = 1 := hz.pow_eq_one
    have h2 : z ^ 2 ≠ 1 := fun h => by
      have := hz.dvd_of_pow_eq_one 2 h
      omega
    have : (z ^ 2 - 1) * (z - Complex.I) * (z + Complex.I) = 0 := by
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      linear_combination h4 - (z ^ 2 - 1) * hI
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd (by linear_combination h) h2
      · simp [Finset.mem_insert, sub_eq_zero.mp h]
    · have : z = -Complex.I := by linear_combination h
      simp [this]
  · intro hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact isPrimitiveRoot_I
    · exact isPrimitiveRoot_neg_I

/-- The sum of the primitive 4-th roots of unity equals `μ(4) = 0`. -/
