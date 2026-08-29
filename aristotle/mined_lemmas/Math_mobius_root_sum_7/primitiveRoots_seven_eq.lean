import Mathlib

/-!
# Mobius Root Sum 7
Category: Pure Mathematics
Target: Math.mobius_root_sum_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- A fixed primitive 7-th root of unity in `ℂ`. -/
private noncomputable def zeta7 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7)


private theorem primitiveRoots_seven_eq :
    primitiveRoots 7 ℂ = (Finset.Ico 1 7).image (fun k => zeta7 ^ k) := by
  have hζ := isPrimitiveRoot_zeta7
  ext x
  simp only [mem_primitiveRoots (by norm_num : 0 < 7), Finset.mem_image, Finset.mem_Ico]
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := hζ.eq_pow_of_pow_eq_one hx.pow_eq_one
    refine ⟨i, ⟨?_, hi⟩, hix⟩
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      simp only [pow_zero] at hix
      exact absurd (hix ▸ hx) (by
        intro h1
        have := h1.unique (IsPrimitiveRoot.one_right_iff.mpr rfl)
        norm_num at this)
    · exact h
  · rintro ⟨k, ⟨hk1, hk7⟩, rfl⟩
    refine hζ.pow_of_coprime k ?_
    interval_cases k <;> decide

