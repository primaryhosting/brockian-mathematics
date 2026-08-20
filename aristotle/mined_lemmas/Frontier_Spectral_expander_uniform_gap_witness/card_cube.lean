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


lemma card_cube (k : ℕ) : Fintype.card (Cube k) = 2 ^ k := by
  simp [Cube, ZMod.card]

/-- **Uniform spectral gap.** There is a single positive constant (namely `2`), independent
of `k`, bounding below every nonzero Laplacian eigenvalue of every hypercube `Q_k`. -/
