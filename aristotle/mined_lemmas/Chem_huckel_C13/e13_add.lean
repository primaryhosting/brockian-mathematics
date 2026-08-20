import Mathlib
/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex Matrix

namespace Chem

/-- A primitive 13-th root of unity. -/

lemma e13_add (a b : ZMod 13) : e13 (a + b) = e13 a * e13 b := by
  simp only [e13, ZMod.val_add, omega13_pow_mod, pow_add]

