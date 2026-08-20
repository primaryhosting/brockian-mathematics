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

lemma charpoly_cycleGraph_five :
    ((SimpleGraph.cycleGraph 5).adjMatrix ℝ).charpoly = X ^ 5 - 5 * X ^ 3 + 5 * X - 2 := by
  rw [Matrix.charpoly, charmatrix_cycleGraph_five]
  simp +decide [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- `cos (2π/5) = (√5 - 1)/4`. -/
