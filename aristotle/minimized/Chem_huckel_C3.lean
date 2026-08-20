/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- The adjacency matrix of the cycle graph `C₃`: every pair of distinct vertices
is joined by an edge, and there are no loops. -/

def C3adj : Matrix (Fin 3) (Fin 3) ℝ := fun i j => if i = j then 0 else 1

/-- Characteristic determinant of `C₃`: `det (A - μ I) = -(μ - 2)(μ + 1)²`. -/
