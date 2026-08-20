import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial Finset

namespace Chem

/-- A primitive 11th root of unity. -/

lemma sum_ee (m : Fin 11) : (∑ l : Fin 11, ee (l * m)) = if m = 0 then 11 else 0 := by
  have h : (∑ l : Fin 11, ee (l * m)) = ∑ i ∈ Finset.range 11, ee m ^ i := by
    rw [← Fin.sum_univ_eq_sum_range fun i => ee m ^ i]
    exact Finset.sum_congr rfl fun l _ => ee_mul l m
  rw [h]
  by_cases hm : m = 0
  · subst hm
    simp [ee_zero]
  · rw [if_neg hm, geom_sum_eq (ee_ne_one hm), ee_pow_eleven, sub_self, zero_div]

/-- Ring identities in `Fin 11 = ZMod 11`. -/
