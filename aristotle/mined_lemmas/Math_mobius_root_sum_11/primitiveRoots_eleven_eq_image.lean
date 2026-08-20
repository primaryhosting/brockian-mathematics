/-
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

namespace Math

open Finset

/-- The primitive `11`-th roots of unity in `ℂ` are exactly the powers `ζ ^ k`
for `1 ≤ k ≤ 10`, where `ζ` is any primitive `11`-th root of unity. -/

lemma primitiveRoots_eleven_eq_image {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 11) :
    primitiveRoots 11 ℂ = (Finset.Ico 1 11).image (fun k => ζ ^ k) := by
  ext x
  simp only [mem_primitiveRoots (by norm_num : (0:ℕ) < 11), Finset.mem_image, Finset.mem_Ico]
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx.pow_eq_one
    refine ⟨k, ⟨?_, hk⟩, rfl⟩
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp only [pow_zero] at hx
      exact absurd rfl (hx.ne_one (by norm_num))
    · exact hpos
  · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
    have hcop : Nat.Coprime k 11 := by interval_cases k <;> decide
    exact hζ.pow_of_coprime k hcop

/-- The sum of the primitive `11`-th roots of unity in `ℂ` equals `μ 11 = -1`. -/
