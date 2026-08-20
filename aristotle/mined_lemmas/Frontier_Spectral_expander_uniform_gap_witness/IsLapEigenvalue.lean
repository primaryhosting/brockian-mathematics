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


def IsLapEigenvalue (k : ℕ) (μ : ℝ) : Prop :=
  ∃ f : Cube k → ℝ, f ≠ 0 ∧ (hypercube k).lapMatrix ℝ *ᵥ f = μ • f

/-- An eigenvector for a nonzero eigenvalue has zero mean. -/
