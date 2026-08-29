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

lemma lapMatrix_mulVec_hypercube {k : ℕ} (f : (Fin k → Bool) → ℝ) (x : Fin k → Bool) :
    ((hypercube k).lapMatrix ℝ *ᵥ f) x = k * f x - ∑ i : Fin k, f (flipAt i x) := by
  rw [SimpleGraph.lapMatrix_mulVec_apply, sum_over_neighbors, hypercube_degree]

/-- The parity function in the first coordinate is an eigenvector for the eigenvalue `2`. -/
