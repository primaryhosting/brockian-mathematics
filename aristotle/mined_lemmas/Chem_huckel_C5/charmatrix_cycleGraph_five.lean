import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the header block
-- above appears immediately after the single `import Mathlib` line.)

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-- The adjacency matrix of the cycle graph `C₅` written out explicitly. -/

lemma charmatrix_cycleGraph_five :
    Matrix.charmatrix ((SimpleGraph.cycleGraph 5).adjMatrix ℝ) =
      !![X, -1, 0, 0, -1;
         -1, X, -1, 0, 0;
         0, -1, X, -1, 0;
         0, 0, -1, X, -1;
         -1, 0, 0, -1, X] := by
  rw [adjMatrix_cycleGraph_five]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.charmatrix]

/-- The characteristic polynomial of the adjacency matrix of `C₅` is `X⁵ - 5X³ + 5X - 2`. -/
