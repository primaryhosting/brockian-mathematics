/-
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- For a primitive `11`-th root of unity `ζ` in `ℂ`, the set of primitive `11`-th roots of
unity is exactly `{ζ ^ 1, ..., ζ ^ 10}`. -/

lemma primitiveRoots_eleven_eq_image {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 11) :
    primitiveRoots 11 ℂ = (Finset.Ico 1 11).image (fun i => ζ ^ i) := by
  ext ξ
  simp only [Finset.mem_image, Finset.mem_Ico, mem_primitiveRoots (by norm_num : 0 < 11)]
  constructor
  · intro hξ
    obtain ⟨i, hi, hpow⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
    refine ⟨i, ⟨?_, hi⟩, hpow⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [pow_zero] at hpow
      subst hpow
      exact absurd (hξ.unique IsPrimitiveRoot.one) (by norm_num)
    · exact hpos
  · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
    refine hζ.pow_of_coprime i ?_
    interval_cases i <;> decide

/-- The sum of the primitive `11`-th roots of unity equals `μ(11)`. -/
