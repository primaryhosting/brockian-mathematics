import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Complex

set_option maxHeartbeats 1000000

namespace Chem

/-- A primitive 14-th root of unity. -/

lemma dft_mul_dftInv : dft * dftInv = 1 := by
  ext j i
  rw [Matrix.mul_apply]
  have hL : ∀ k : Fin 14, dft j k * dftInv k i = (14 : ℂ)⁻¹ * chi (k * (j - i)) := by
    intro k
    have h : k * (j - i) = k * j - k * i := mul_sub k j i
    rw [dft, dftInv, h, chi_sub]
    ring
  rw [Finset.sum_congr rfl fun k _ => hL k, ← Finset.mul_sum, chi_sum]
  by_cases h : j = i
  · subst h
    simp
  · have hji : j - i ≠ 0 := sub_ne_zero_of_ne h
    rw [if_neg hji]
    simp [h]

