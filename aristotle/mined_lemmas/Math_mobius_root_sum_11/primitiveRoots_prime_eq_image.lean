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

namespace Math

open Finset

/-- For a prime `p` and a primitive `p`-th root of unity `ζ` in a domain, the set of primitive
`p`-th roots of unity is exactly `{ζ ^ i : 1 ≤ i < p}`. -/

lemma primitiveRoots_prime_eq_image {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R] {p : ℕ}
    (hp : p.Prime) {ζ : R} (hζ : IsPrimitiveRoot ζ p) :
    primitiveRoots p R = (Finset.Ico 1 p).image (fun i => ζ ^ i) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  ext z
  simp only [mem_primitiveRoots hp.pos, Finset.mem_image, Finset.mem_Ico]
  constructor
  · intro hz
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz.pow_eq_one
    refine ⟨i, ⟨?_, hi⟩, rfl⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact absurd (hz.unique (by simp)) hp.one_lt.ne'
    · exact hi0
  · rintro ⟨i, ⟨hi1, hip⟩, rfl⟩
    exact hζ.pow_of_coprime i
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2
        (Nat.not_dvd_of_pos_of_lt hi1 hip)))

/-- The sum of the primitive `p`-th roots of unity in a domain containing a primitive `p`-th
root of unity, for `p` prime, equals `-1`. -/
