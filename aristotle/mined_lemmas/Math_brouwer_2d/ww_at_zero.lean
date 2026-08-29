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

theorem ww_at_zero (t : ℝ) : ww f 0 t = -f 0 := by
  rw [ww, aa_zero, bb_zero]
  push_cast
  simp

end Main

/-- **Brouwer's fixed point theorem** in dimension 2, complex formulation. -/
