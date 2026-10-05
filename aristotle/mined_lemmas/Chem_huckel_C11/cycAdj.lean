/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Complex Finset

namespace Chem

/-- The circulant form of the adjacency matrix of the cycle graph `C₁₁`,
with vertices indexed by `ZMod 11`. -/

noncomputable def cycAdj : Matrix (ZMod 11) (ZMod 11) ℂ :=
  Matrix.circulant (fun d => if d = 1 ∨ d = -1 then 1 else 0)

/-- The adjacency matrix of `SimpleGraph.cycleGraph 11` is the circulant matrix `cycAdj`. -/
