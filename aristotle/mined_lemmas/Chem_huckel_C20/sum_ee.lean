import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Matrix Polynomial Finset

/-- A primitive 20-th root of unity. -/

lemma sum_ee (m : Fin 20) : (∑ k : Fin 20, ee (m * k)) = if m = 0 then 20 else 0 := by
  have h1 : (∑ k : Fin 20, ee (m * k)) = ∑ j ∈ Finset.range 20, (ee m) ^ j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (ee m) ^ j) 20]
    exact Finset.sum_congr rfl (fun k _ => ee_mul_pow m k)
  rw [h1]
  by_cases hm : m = 0
  · subst hm
    simp [ee_zero]
  · rw [if_neg hm]
    have hne : ee m ≠ 1 := fun h => hm ((ee_eq_one_iff m).mp h)
    rw [geom_sum_eq hne, ee_pow_twenty, sub_self, zero_div]

/-- The DFT matrix. -/
