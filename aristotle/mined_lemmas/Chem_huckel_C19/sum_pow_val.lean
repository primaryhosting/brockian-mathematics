import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Matrix

namespace Chem

/-- A primitive 19-th root of unity. -/

lemma sum_pow_val (z : ℂ) (hz : z ^ 19 = 1) :
    ∑ j : Fin 19, z ^ (j : ℕ) = if z = 1 then (19 : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => z ^ j) 19]
  by_cases h : z = 1
  · simp [h]
  · rw [geom_sum_eq h, hz, sub_self, zero_div, if_neg h]

