import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix SimpleGraph

/-- A primitive 17-th root of unity. -/

lemma adjMatrix_complex_eq_map :
    ((cycleGraph 17).adjMatrix ℂ)
      = ((cycleGraph 17).adjMatrix ℝ).map (Complex.ofRealHom : ℝ →+* ℂ) := by
  ext j k
  simp [Matrix.map_apply, SimpleGraph.adjMatrix_apply]

/-- **Hückel theory for the C₁₇ ring.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₇` factors as `∏ (X - 2 cos (2πk/17))`, i.e. the adjacency
eigenvalues of `C₁₇` are exactly `2 cos (2πk/17)` for `k = 0, …, 16`. -/
