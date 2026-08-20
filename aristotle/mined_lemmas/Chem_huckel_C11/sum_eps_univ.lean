/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- A primitive 11-th root of unity. -/

lemma sum_eps_univ : ∑ k : ZMod 11, eps k = 0 := by
  have h : ∑ k : ZMod 11, eps k = ∑ i ∈ Finset.range 11, zeta ^ i := by
    have h2 : ∑ k : ZMod 11, eps k = ∑ i : Fin 11, zeta ^ (i : ℕ) := rfl
    rw [h2, Fin.sum_univ_eq_sum_range]
  rw [h, zeta_primitive.geom_sum_eq_zero (by norm_num)]

