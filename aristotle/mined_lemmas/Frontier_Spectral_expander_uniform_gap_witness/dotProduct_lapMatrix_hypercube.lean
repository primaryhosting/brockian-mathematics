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

open Finset Matrix

/-! ## The hypercube graph -/

/-- Flip the `i`-th coordinate of a point of the discrete cube `Fin k → Bool`. -/

lemma dotProduct_lapMatrix_hypercube {k : ℕ} (f : (Fin k → Bool) → ℝ) :
    f ⬝ᵥ ((hypercube k).lapMatrix ℝ *ᵥ f) = dirichlet k f / 2 := by
  rw [← Matrix.toLinearMap₂'_apply', SimpleGraph.lapMatrix_toLinearMap₂', dirichlet]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← sum_ite_adj (fun y => (f x - f y) ^ 2) x]

/-! ## Splitting the cube along the first coordinate -/

