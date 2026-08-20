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


theorem expander_uniform_gap_witness :
    ∀ k : ℕ, 1 ≤ k → IsLeast {μ : ℝ | IsLapEigenvalue k μ ∧ μ ≠ 0} 2 := by
  intro k hk
  constructor
  · exact ⟨two_isLapEigenvalue hk, by norm_num⟩
  · rintro μ ⟨hev, hμ⟩
    exact two_le_of_isLapEigenvalue hμ hev

/-- The hypercube `Q_k` has `2 ^ k` vertices. -/
