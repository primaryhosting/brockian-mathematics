/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Complex

namespace Chem

/-- A primitive 18-th root of unity. -/

theorem ch_sum (m : Fin 18) : (∑ k : Fin 18, ch (k * m)) = if m = 0 then 18 else 0 := by
  simp only [ch_mul_pow]
  rw [Fin.sum_univ_eq_sum_range (fun i => (ch m) ^ i) 18]
  by_cases hm : m = 0
  · simp [hm, ch_zero]
  · have hz : ch m ≠ 1 := by
      simp only [ch]
      exact om_primitive.pow_ne_one_of_pos_of_lt (by omega) m.isLt
    have h18 : (ch m) ^ 18 = 1 := by
      simp only [ch]
      rw [← pow_mul, mul_comm, pow_mul, om_pow_eighteen, one_pow]
    rw [geom_sum_eq hz, h18, if_neg hm]
    simp

