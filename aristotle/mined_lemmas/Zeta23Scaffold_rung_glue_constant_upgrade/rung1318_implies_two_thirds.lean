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

theorem rung1318_implies_two_thirds (n s : ℝ → ℝ) (hn : ∀ T, 0 ≤ n T)
    (H : EventualBound (13 / 18) n s) :
    EventualBound (2 / 3) n s := by
  intro ε hε
  obtain ⟨T0, hT0⟩ := H ε hε
  refine ⟨T0, fun T hT => ?_⟩
  have h := hT0 T hT
  have hmono : (2 / 3 - ε) * n T ≤ (13 / 18 - ε) * n T := by
    have : (2 / 3 - ε) ≤ (13 / 18 - ε) := by norm_num
    exact mul_le_mul_of_nonneg_right this (hn T)
  linarith

/-- **Rung glue constant upgrade.**  For any nonnegative comparison sequence `n`,
the `(2*(31/36) - 1 - ε)`-bound yields both the `(13/18 - ε)`-bound and the
`(2/3 - ε)`-bound. -/
