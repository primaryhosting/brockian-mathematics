import Mathlib
/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Matrix

namespace Chem

/-- The Hückel (adjacency) matrix of the cycle `C₄`: `A i j = 1` exactly when the carbon
atoms `i` and `j` are neighbours in the four-membered ring. -/

lemma C4_eq : C4 = !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C4] <;> decide

