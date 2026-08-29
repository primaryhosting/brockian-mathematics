/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- `g n = exp (2πi n / 19)`, the basic 19-th root of unity raised to `n`. -/

lemma z19_sum_ne_zero {c : ZMod 19} (hc : c ≠ 0) : ∑ k : ZMod 19, z19 (c * k) = 0 := by
  set s : ℂ := ∑ k : ZMod 19, z19 (c * k) with hs
  have hstep : s * z19 c = s := by
    have := Equiv.sum_comp (Equiv.addRight (1 : ZMod 19)) (fun k : ZMod 19 => z19 (c * k))
    rw [hs, Finset.sum_mul]
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : c * (k + 1) = c * k + c := by ring
    simp only [Equiv.coe_addRight, this, z19_add]
  have : s * (z19 c - 1) = 0 := by ring_nf; linear_combination hstep
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · exact absurd (by linear_combination h) (z19_ne_one hc)

