/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Finset

/-- A primitive 16-th root of unity. -/

lemma zeta_eq_one_iff (a : ZMod 16) : zeta a = 1 ↔ a = 0 := by
  constructor
  · intro h
    by_contra hne
    have hval : a.val ≠ 0 := by
      intro h0
      apply hne
      rw [← ZMod.natCast_zmod_val a, h0]
      simp
    have hlt : a.val < 16 := ZMod.val_lt a
    exact (w_prim.pow_ne_one_of_pos_of_lt hval hlt) h
  · rintro rfl; exact zeta_zero

