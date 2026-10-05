import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- A primitive ninth root of unity. -/

lemma ec_ne_one {c : ZMod 9} (hc : c ≠ 0) : ec c ≠ 1 := by
  intro h
  rw [ec, zeta9_isPrimitiveRoot.pow_eq_one_iff_dvd] at h
  have h9 : c.val < 9 := ZMod.val_lt c
  have hv : c.val = 0 := by rcases h with ⟨m, hm⟩; omega
  exact hc ((ZMod.val_eq_zero c).mp hv)

/-- Character sum: `∑_x e(c x) = 0` for `c ≠ 0`. -/
