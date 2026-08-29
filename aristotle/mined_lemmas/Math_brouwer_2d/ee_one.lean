import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Metric Set

namespace Brouwer2D

noncomputable section

/-- The punctured complex plane, the base of the exponential covering map. -/
abbrev Cstar := {z : ℂ // z ≠ 0}

/-- The exponential covering map `ℂ → ℂ \ {0}`. -/

theorem ee_one : ee 1 = 1 := by
  have : ((2 * Real.pi * 1 : ℝ) : ℂ) * Complex.I = 2 * Real.pi * Complex.I := by
    push_cast; ring
  rw [ee, this, Complex.exp_two_pi_mul_I]

/-- Clamped parameter controlling the radius. -/
