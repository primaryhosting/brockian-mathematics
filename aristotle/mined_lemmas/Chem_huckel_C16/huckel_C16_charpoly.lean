import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
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

/-- The Hückel (adjacency) matrix of the cycle graph `C₁₆`, over `ℝ`. -/

theorem huckel_C16_charpoly :
    huckelMatrix.charpoly = ∏ k : Fin 16, (X - C (huckelEigenvalue k)) := by
  apply Polynomial.map_injective (Complex.ofRealHom : ℝ →+* ℂ) Complex.ofReal_injective
  rw [← Matrix.charpoly_map, adjMatrix_map, charpoly_complex, Polynomial.map_prod]
  simp

/-- **Hückel theory for the C₁₆ annulene.**  The characteristic polynomial of the adjacency
(Hückel) matrix of the cycle graph `C₁₆` factors completely as `∏_{k=0}^{15} (X - 2cos(2πk/16))`;
consequently the set of adjacency eigenvalues of `C₁₆` is exactly
`{2 cos (2πk/16) : k = 0, …, 15}`. -/
