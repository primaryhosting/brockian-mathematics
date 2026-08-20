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
lemma sum_primitiveRoots_prime {R : Type*} [CommRing R] [IsDomain R] {p : ℕ}
    (hp : p.Prime) {ζ : R} (hζ : IsPrimitiveRoot ζ p) :
    ∑ z ∈ primitiveRoots p R, z = -1 := by
  classical
  rw [primitiveRoots_prime_eq_image hp hζ,
    Finset.sum_image (fun i hi j hj h => hζ.pow_inj (by simp at hi; omega)
      (by simp at hj; omega) h)]
  have h0 : ∑ i ∈ Finset.range p, ζ ^ i = 0 := hζ.geom_sum_eq_zero hp.one_lt
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hp.pos] at h0
  simp only [pow_zero] at h0
  linear_combination h0

/-- **Mobius Root Sum 11.** The sum of the primitive 11-th roots of unity equals `μ(11) = -1`. -/
theorem mobius_root_sum_11 :
    ∑ z ∈ primitiveRoots 11 ℂ, z = (ArithmeticFunction.moebius 11 : ℂ) := by
  have hp : Nat.Prime 11 := by norm_num
  rw [sum_primitiveRoots_prime hp (Complex.isPrimitiveRoot_exp 11 (by norm_num)),
    ArithmeticFunction.moebius_apply_prime hp]
  norm_num

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

