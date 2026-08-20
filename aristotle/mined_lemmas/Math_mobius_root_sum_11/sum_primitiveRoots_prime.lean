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
