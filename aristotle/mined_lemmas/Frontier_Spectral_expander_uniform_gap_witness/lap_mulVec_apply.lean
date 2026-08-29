/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

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

namespace Frontier.Spectral

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`. -/
abbrev Cube (k : ℕ) : Type := Fin k → Bool

/-- Flip the `i`-th coordinate of a vertex of the hypercube. -/

lemma lap_mulVec_apply {k : ℕ} (v : Cube k → ℝ) (x : Cube k) :
    ((hypercube k).lapMatrix ℝ).mulVec v x = k * v x - ∑ i : Fin k, v (cflip x i) := by
  rw [SimpleGraph.lapMatrix, Matrix.sub_mulVec]
  simp only [Pi.sub_apply, SimpleGraph.adjMatrix_mulVec_apply, sum_over_neighbors]
  congr 1
  rw [SimpleGraph.degMatrix, Matrix.mulVec_diagonal, hypercube_degree]

/-- The `cflip` map along a fixed coordinate is a bijection of the cube. -/
