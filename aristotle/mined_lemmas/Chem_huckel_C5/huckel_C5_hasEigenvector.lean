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

theorem huckel_C5_hasEigenvector (k : Fin 5) :
    ∃ v : Fin 5 → ℝ, v ≠ 0 ∧
      (SimpleGraph.cycleGraph 5).adjMatrix ℝ *ᵥ v
        = (2 * Real.cos (2 * π * ((k : ℕ) : ℝ) / 5)) • v := by
  refine exists_eigenvector_of_isRoot_charpoly ?_
  rw [huckel_C5, eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
  simp

end Chem

