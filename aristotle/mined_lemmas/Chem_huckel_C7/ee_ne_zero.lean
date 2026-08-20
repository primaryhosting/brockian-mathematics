import Mathlib
/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Chem

open Complex Finset Matrix

/-- A primitive 7-th root of unity. -/

lemma ee_ne_zero (a : Fin 7) : ee a ≠ 0 := by
  simp only [ee, zeta]
  exact pow_ne_zero _ (Complex.exp_ne_zero _)

