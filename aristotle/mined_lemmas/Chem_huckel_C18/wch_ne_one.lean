/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Polynomial Finset

noncomputable section

/-- A primitive 18-th root of unity. -/

theorem wch_ne_one {c : ZMod 18} (hc : c ≠ 0) : wch c ≠ 1 := by
  have hv : c.val ≠ 0 := fun h => hc (by
    have := ZMod.natCast_zmod_val c
    rw [h] at this; simpa using this.symm)
  exact isPrimitiveRoot_zeta.pow_ne_one_of_pos_of_lt hv (ZMod.val_lt c)

