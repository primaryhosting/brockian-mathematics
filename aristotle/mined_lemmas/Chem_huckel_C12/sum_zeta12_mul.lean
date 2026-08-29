import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma sum_zeta12_mul (m : ZMod 12) :
    ∑ k : ZMod 12, zeta12 (k * m) = if m = 0 then 12 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [zeta12_zero]
  · rw [if_neg hm, sum_univ_zmod12 (fun k => zeta12 (k * m))]
    have h : ∀ n ∈ Finset.range 12, zeta12 ((n : ZMod 12) * m) = zeta12 m ^ n := by
      intro n _; exact zeta12_natCast_mul n m
    rw [Finset.sum_congr rfl h, geom_sum_eq (zeta12_ne_one hm), zeta12_pow_twelve]
    simp

/-- The (unnormalised) discrete Fourier transform matrix. -/
