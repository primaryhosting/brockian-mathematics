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

lemma ee_ne_zero (a : ZMod 15) : ee a ≠ 0 := by
  have : zeta ≠ 0 := by
    intro h
    have := zeta_pow_15
    rw [h] at this
    simp at this
  exact pow_ne_zero _ this

