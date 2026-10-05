import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Real Matrix Finset

/-- A primitive 18-th root of unity. -/

lemma ee_sum (c : ZMod 18) : ∑ j : ZMod 18, ee (j * c) = if c = 0 then 18 else 0 := by
  have hstep : ∑ j : ZMod 18, ee (j * c) = ∑ i ∈ Finset.range 18, (ee c) ^ i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun x _ => ee_mul x c)
  rw [hstep]
  by_cases hc : c = 0
  · simp [hc, ee_zero]
  · rw [if_neg hc, geom_sum_eq (ee_ne_one c hc), ee_pow_18, sub_self, zero_div]

/-- `ee k + ee (-k) = 2 cos (2πk/18)`. -/
