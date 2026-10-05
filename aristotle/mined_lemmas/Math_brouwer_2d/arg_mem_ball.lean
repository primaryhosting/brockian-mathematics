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

theorem arg_mem_ball (s t : ℝ) : (aa s : ℂ) * ee t ∈ closedBall (0 : ℂ) 1 := by
  simpa [mem_closedBall, dist_eq_norm] using norm_arg_le_one s t

