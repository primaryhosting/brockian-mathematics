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
