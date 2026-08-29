/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 4000000

namespace Chem

/-- A primitive 8-th root of unity. -/

lemma Fmat_mul_Gmat : Fmat * Gmat = 1 := by
  ext k l
  rw [Matrix.mul_apply]
  have hterm : ∀ j : Fin 8,
      Fmat k j * Gmat j l = zeta ^ ((j : ℕ) * ((k : ℕ) + 7 * (l : ℕ))) / 8 := by
    intro j
    simp only [Fmat, Gmat, mul_div_assoc', ← pow_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.sum_div]
  by_cases h : ((k : ℕ) + 7 * (l : ℕ)) % 8 = 0
  · have hkl : k = l := (mod_eight_iff k l).1 h
    subst hkl
    rw [geom_sum_zeta_eq_eight _ h, Matrix.one_apply_eq]
    norm_num
  · rw [geom_sum_zeta_eq_zero _ h, Matrix.one_apply_ne (fun hkl => h ((mod_eight_iff k l).2 hkl))]
    norm_num

