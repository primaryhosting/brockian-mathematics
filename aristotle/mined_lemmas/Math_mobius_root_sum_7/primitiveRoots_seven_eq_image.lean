import Mathlib

/-!
# Mobius Root Sum 7
Category: Pure Mathematics
Target: Math.mobius_root_sum_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ArithmeticFunction

namespace Math

/-- For a primitive `7`-th root of unity `ζ`, the primitive `7`-th roots of unity are
exactly `ζ ^ i` for `1 ≤ i < 7`. -/

lemma primitiveRoots_seven_eq_image {ζ : ℂ} (h : IsPrimitiveRoot ζ 7) :
    primitiveRoots 7 ℂ = (Finset.Ico 1 7).image (fun i => ζ ^ i) := by
  ext x
  simp only [mem_primitiveRoots (by norm_num : (0:ℕ) < 7), Finset.mem_image, Finset.mem_Ico]
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := h.eq_pow_of_pow_eq_one hx.pow_eq_one
    refine ⟨i, ⟨?_, hi⟩, rfl⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp only [pow_zero] at hx
      exact absurd (hx.unique IsPrimitiveRoot.one) (by norm_num)
    · exact hpos
  · rintro ⟨i, ⟨hi1, hi7⟩, rfl⟩
    refine h.pow_of_coprime i ?_
    interval_cases i <;> decide

/-- The sum of the primitive `7`-th roots of unity equals `μ 7 = -1`. -/
