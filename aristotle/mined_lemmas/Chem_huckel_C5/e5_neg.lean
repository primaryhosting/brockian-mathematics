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

lemma e5_neg (m : ZMod 5) : e5 (-m) = (e5 m)⁻¹ := by
  have h : e5 m * e5 (-m) = 1 := by rw [← e5_add]; simp [e5_zero]
  field_simp [e5_ne_zero m]
  linear_combination h

