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


theorem hypercube_uniform_spectral_gap :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∀ μ : ℝ, IsLapEigenvalue k μ → μ ≠ 0 → c ≤ μ :=
  ⟨2, by norm_num, fun _ _ _ hev hμ => two_le_of_isLapEigenvalue hμ hev⟩

end Frontier.Spectral

