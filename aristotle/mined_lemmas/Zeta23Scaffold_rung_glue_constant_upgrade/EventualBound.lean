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

def EventualBound (c : ℝ) (n s : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ T0 : ℝ, ∀ T ≥ T0, (c - ε) * n T ≤ s T

/-- (a) The `(2*(31/36) - 1 - ε)`-bound is literally the `(13/18 - ε)`-bound. -/
