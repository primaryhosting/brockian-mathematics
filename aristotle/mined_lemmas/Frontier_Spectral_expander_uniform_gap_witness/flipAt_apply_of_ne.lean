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


lemma flipAt_apply_of_ne {k : ℕ} {i j : Fin k} (h : j ≠ i) (x : Cube k) :
    flipAt i x j = x j := by
  simp [flipAt, Function.update_of_ne h]

