/-
# Rung Glue Constant Upgrade
Category: A Assembly
Target: Zeta23Scaffold.rung_glue_constant_upgrade
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Scaffold

/-- Abbreviation for the eventual lower bound statement
`∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c - ε) * n T ≤ s T`. -/

theorem rung1318_of_bridge (n s : ℝ → ℝ)
    (H : ∀ ε > 0, ∃ T0 : ℝ, ∀ T ≥ T0, (2 * (31 / 36) - 1 - ε) * n T ≤ s T) :
    EventualBound (13 / 18) n s := by
  intro ε hε
  obtain ⟨T0, hT0⟩ := H ε hε
  refine ⟨T0, fun T hT => ?_⟩
  have h := hT0 T hT
  have hc : (2 * (31 / 36) - 1 - ε : ℝ) = 13 / 18 - ε := by norm_num
  rwa [hc] at h

/-- (b) The `(13/18 - ε)`-bound dominates the `(2/3 - ε)`-bound, for a nonnegative
comparison sequence `n`. -/
