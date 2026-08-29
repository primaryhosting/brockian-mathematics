import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- A primitive 15-th root of unity. -/

noncomputable def Pm : Matrix (Fin 15) (Fin 15) ℂ := Matrix.of fun i l => (g i) ^ (l.val)

/-- The inverse DFT matrix. -/
