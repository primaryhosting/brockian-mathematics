/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset

/-- A primitive 15-th root of unity. -/

lemma ee_sum (m : ZMod 15) : ∑ k : ZMod 15, ee (k * m) = if m = 0 then 15 else 0 := by
  by_cases hm : m = 0
  · subst hm; simp [ee_zero, ZMod.card]
  · rw [if_neg hm]
    have hshift : ∑ k : ZMod 15, ee ((k + 1) * m) = ∑ k : ZMod 15, ee (k * m) :=
      Equiv.sum_comp (Equiv.addRight (1 : ZMod 15)) (fun k => ee (k * m))
    have hexp : ∀ k : ZMod 15, ee ((k + 1) * m) = ee (k * m) * ee m := by
      intro k
      rw [← ee_add]; ring_nf
    rw [Finset.sum_congr rfl (fun k _ => hexp k), ← Finset.sum_mul] at hshift
    have : (∑ k : ZMod 15, ee (k * m)) * (ee m - 1) = 0 := by
      rw [mul_sub, mul_one, hshift, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (by linear_combination h) (ee_ne_one hm)

