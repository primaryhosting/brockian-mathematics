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

lemma ec_add (x y : ZMod 9) : ec (x + y) = ec x * ec y := by
  simp only [ec, ZMod.val_add, zeta9_pow_mod, pow_add]

