/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset

/-- A primitive 15-th root of unity. -/

lemma ee_add (a b : ZMod 15) : ee (a + b) = ee a * ee b := by
  simp [ee, ZMod.val_add, zeta_pow_mod, pow_add]

