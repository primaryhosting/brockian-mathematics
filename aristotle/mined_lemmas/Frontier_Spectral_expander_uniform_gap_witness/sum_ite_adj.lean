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

lemma sum_ite_adj {k : ℕ} (f : (Fin k → Bool) → ℝ) (x : Fin k → Bool) :
    ∑ y : Fin k → Bool, (if (hypercube k).Adj x y then f y else 0)
      = ∑ i : Fin k, f (flipAt i x) := by
  rw [← Finset.sum_filter]
  have h : Finset.univ.filter (fun y => (hypercube k).Adj x y)
      = (hypercube k).neighborFinset x := by
    ext y; simp [SimpleGraph.mem_neighborFinset]
  rw [h, sum_over_neighbors]

/-- The hypercube `Q_k` has `2 ^ k` vertices. -/
