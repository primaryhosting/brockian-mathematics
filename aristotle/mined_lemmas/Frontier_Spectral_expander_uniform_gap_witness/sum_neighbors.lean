/-
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Matrix

set_option maxHeartbeats 1000000

namespace Frontier.Spectral

/-! ## The hypercube graph -/

/-- The vertex set of the `k`-dimensional hypercube: binary strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2


lemma sum_neighbors {k : ℕ} (x : Cube k) (g : Cube k → ℝ) :
    ∑ u ∈ (hypercube k).neighborFinset x, g u = ∑ i : Fin k, g (flipAt i x) := by
  rw [neighborFinset_eq, Finset.sum_image]
  intro i _ j _ h
  exact flipAt_injective x h

