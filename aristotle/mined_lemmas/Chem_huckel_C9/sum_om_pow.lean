import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Polynomial

namespace Chem

/-- A primitive 9th root of unity. -/

theorem sum_om_pow (t : ℕ) :
    ∑ k : Fin 9, (om ^ t) ^ (k : ℕ) = if t % 9 = 0 then (9 : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (om ^ t) ^ i) 9]
  by_cases ht : t % 9 = 0
  · have h1 : om ^ t = 1 := by rw [← om_pow_mod, ht, pow_zero]
    simp [h1, ht]
  · rw [if_neg ht, geom_sum_eq (om_pow_ne_one ht), om_pow_pow_nine, sub_self, zero_div]

/-- The DFT matrix. -/
