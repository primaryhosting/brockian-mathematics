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

lemma adjMatrix_map :
    ((cycleGraph 7).adjMatrix ℝ).map (Complex.ofRealHom : ℝ →+* ℂ)
      = (cycleGraph 7).adjMatrix ℂ := by
  ext i j
  by_cases h : (cycleGraph 7).Adj i j <;>
    simp [Matrix.map_apply, SimpleGraph.adjMatrix_apply, h]

/-- The characteristic polynomial of the adjacency matrix of the cycle graph `C₇`
splits with roots `2 cos (2πk/7)` for `k = 0, …, 6`: these are the Hückel (adjacency)
eigenvalues of `C₇`, listed with multiplicity. -/
