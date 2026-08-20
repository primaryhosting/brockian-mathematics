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


@[simp] lemma degree_hypercube {k : ℕ} (x : Cube k) : (hypercube k).degree x = k := by
  rw [SimpleGraph.degree, neighborFinset_eq,
    Finset.card_image_of_injective _ (flipAt_injective x), Finset.card_univ, Fintype.card_fin]

/-! ## The Dirichlet form and the Poincaré inequality -/

/-- The Dirichlet form of the hypercube: `∑_x ∑_i (f x - f (flip i x))^2`. -/
