/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset Complex

/-- A primitive 14-th root of unity. -/

lemma eq_zero_of_fourier_zero (v : ZMod 14 → ℂ)
    (h : ∀ k : ZMod 14, ∑ j : ZMod 14, v j * ch (-(k * j)) = 0) : v = 0 := by
  funext i
  have key : ∑ k : ZMod 14, (∑ j : ZMod 14, v j * ch (-(k * j))) * ch (k * i)
      = 14 * v i := by
    have step : ∀ k : ZMod 14, (∑ j : ZMod 14, v j * ch (-(k * j))) * ch (k * i)
        = ∑ j : ZMod 14, v j * ch ((i - j) * k) := by
      intro k
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_assoc, ← ch_add]
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun k _ => step k), Finset.sum_comm]
    have inner : ∀ j : ZMod 14, ∑ k : ZMod 14, v j * ch ((i - j) * k)
        = if j = i then 14 * v j else 0 := by
      intro j
      rw [← Finset.mul_sum, sum_ch]
      by_cases hj : j = i
      · subst hj; simp [mul_comm]
      · have hij : i - j ≠ 0 := fun hc => hj (by linear_combination -hc)
        simp [hij, hj]
    rw [Finset.sum_congr rfl (fun j _ => inner j)]
    simp
  rw [Finset.sum_congr rfl (fun k _ => by rw [h k, zero_mul])] at key
  simp only [Finset.sum_const_zero] at key
  have h14 : (14 : ℂ) * v i = 0 := key.symm
  have hvi : v i = 0 := by
    rcases mul_eq_zero.1 h14 with h' | h'
    · norm_num at h'
    · exact h'
  simpa using hvi

