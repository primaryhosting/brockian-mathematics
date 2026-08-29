/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Chem

/-- A primitive fifth root of unity. -/

lemma e5_ne_zero (m : ZMod 5) : e5 m ≠ 0 := by
  have : zeta5 ≠ 0 := by
    simp [zeta5, Complex.exp_ne_zero]
  exact pow_ne_zero _ this

