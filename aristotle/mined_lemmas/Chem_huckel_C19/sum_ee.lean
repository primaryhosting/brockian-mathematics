/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex (I)
open Matrix

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

theorem sum_ee (d : Fin 19) : ∑ k : Fin 19, ee (k * d) = if d = 0 then 19 else 0 := by
  simp only [ee_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => ee d ^ i) 19]
  by_cases hd : d = 0
  · subst hd
    simp [ee_zero]
  · rw [if_neg hd, geom_sum_eq (ee_ne_one hd), ee_pow_19, sub_self, zero_div]

