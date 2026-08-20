import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial Finset

namespace Chem

/-- A primitive 11th root of unity. -/

lemma ee_add (a b : Fin 11) : ee (a + b) = ee a * ee b := by
  unfold ee
  rw [Fin.val_add, zeta_pow_mod, pow_add]

