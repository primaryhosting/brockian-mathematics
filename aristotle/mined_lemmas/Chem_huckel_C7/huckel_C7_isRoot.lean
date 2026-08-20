/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix SimpleGraph

/-! ### A primitive 7th root of unity -/

/-- A primitive 7th root of unity. -/

theorem huckel_C7_isRoot {k : ℕ} (hk : k < 7) :
    ((cycleGraph 7).adjMatrix ℝ).charpoly.IsRoot (2 * Real.cos (2 * Real.pi * k / 7)) := by
  rw [Polynomial.IsRoot, huckel_C7, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_range.mpr hk) ?_
  simp

end Chem

