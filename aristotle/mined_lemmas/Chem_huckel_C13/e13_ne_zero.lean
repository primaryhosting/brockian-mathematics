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

lemma e13_ne_zero (a : ZMod 13) : e13 a ≠ 0 := by
  simp only [e13]
  exact pow_ne_zero _ (Complex.exp_ne_zero _)

