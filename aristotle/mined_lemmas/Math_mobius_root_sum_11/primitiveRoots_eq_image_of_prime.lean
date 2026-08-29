/-
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- For a primitive `p`-th root of unity `ζ` with `p` prime, the primitive `p`-th roots of
unity are exactly the powers `ζ ^ i` with `1 ≤ i < p`. -/

lemma primitiveRoots_eq_image_of_prime {p : ℕ} (hp : p.Prime) {ζ : ℂ}
    (h : IsPrimitiveRoot ζ p) :
    primitiveRoots p ℂ = (Finset.Ico 1 p).image (fun i => ζ ^ i) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  ext x
  simp only [Finset.mem_image, Finset.mem_Ico, mem_primitiveRoots hp.pos]
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := h.eq_pow_of_pow_eq_one hx.pow_eq_one
    refine ⟨i, ⟨?_, hi⟩, hix⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exfalso
      simp only [pow_zero] at hix
      exact hx.pow_ne_one_of_pos_of_lt one_ne_zero hp.one_lt (by simp [← hix])
    · exact hpos
  · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
    refine h.pow_of_coprime i (Nat.Coprime.symm ((hp.coprime_iff_not_dvd).mpr ?_))
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega

/-- The sum of the primitive 11-th roots of unity in `ℂ` equals `μ 11 = -1`. -/
