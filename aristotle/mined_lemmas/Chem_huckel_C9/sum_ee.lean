import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

noncomputable section

/-- A primitive 9-th root of unity. -/

lemma sum_ee (c : ZMod 9) : ∑ j : ZMod 9, ee (c * j) = if c = 0 then 9 else 0 := by
  by_cases hc : c = 0
  · simp [hc, ee_zero]
  · simp only [hc, if_false]
    have h : ∑ j : ZMod 9, ee (c * j) = ∑ m ∈ Finset.range 9, (ee c) ^ m := by
      simp only [ee_pow]
      exact Fin.sum_univ_eq_sum_range (fun m => (ee c) ^ m) 9
    rw [h, geom_sum_eq (ee_ne_one hc), ee_pow_nine, sub_self, zero_div]

