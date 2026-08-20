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

namespace Chem

open Matrix

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₈`. -/

lemma C8adj_map_complex :
    C8adj.map (Complex.ofRealHom : ℝ →+* ℂ) = (SimpleGraph.cycleGraph 8).adjMatrix ℂ := by
  ext i j
  simp [C8adj, SimpleGraph.adjMatrix, apply_ite (Complex.ofRealHom : ℝ →+* ℂ)]

open Polynomial in
/-- **The Hückel spectrum of C₈ with multiplicities.**  The characteristic polynomial of the
adjacency matrix of the cycle graph `C₈` is `∏_{k=0}^{7} (X - 2 cos (2πk/8))`; equivalently the
eight eigenvalues, listed with multiplicity, are `2 cos (2πk/8)` for `k = 0, …, 7`. -/
