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

theorem norm_arg_le_one (s t : ℝ) : ‖(aa s : ℂ) * ee t‖ ≤ 1 := by
  rw [norm_mul, norm_ee, Complex.norm_real, Real.norm_eq_abs, mul_one,
    abs_of_nonneg (aa_nonneg s)]
  exact aa_le_one s

