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

theorem ee_add (a b : Fin 19) : ee (a + b) = ee a * ee b := by
  simp only [ee, Fin.val_add, om_pow_mod, pow_add]

