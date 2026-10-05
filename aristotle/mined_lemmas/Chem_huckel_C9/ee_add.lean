import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

noncomputable section

/-- A primitive 9-th root of unity. -/

lemma ee_add (a b : ZMod 9) : ee (a + b) = ee a * ee b := by
  simp only [ee, ZMod.val_add, om_pow_mod, pow_add]

