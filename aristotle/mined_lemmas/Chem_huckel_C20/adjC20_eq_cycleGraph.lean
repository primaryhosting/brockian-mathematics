/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring `/-! ... -/` before the `import`
line, so the required header appears here as an ordinary block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix

/-! ### The primitive 20-th root of unity and the associated character -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

lemma adjC20_eq_cycleGraph : adjC20 = (SimpleGraph.cycleGraph 20).adjMatrix ℂ := by
  ext i j
  simp only [adjC20, Matrix.of_apply, SimpleGraph.adjMatrix_apply]
  congr 1
  simp [SimpleGraph.cycleGraph_adj]

/-- The DFT matrix. -/
