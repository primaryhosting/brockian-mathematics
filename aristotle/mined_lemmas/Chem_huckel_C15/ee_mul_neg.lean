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

lemma ee_mul_neg (a : ZMod 15) : ee a * ee (-a) = 1 := by
  rw [← ee_add]; simp [ee_zero]

