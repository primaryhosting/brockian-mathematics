/-
  CompactCriterion.lean — an abstract compactness criterion: an operator whose
  unit-ball image is uniformly approximable by finite-dimensional subspaces is
  a compact operator.
-/
import Mathlib

open Metric Filter

namespace Brockian.Weyl.OscillatorCompact

/-- An operator whose closed-unit-ball image is uniformly approximable by
finite-dimensional subspaces is a compact operator. -/

theorem deriv_continuous (g : SchwartzMap ℝ ℂ) : Continuous (deriv (g : ℝ → ℂ)) := by
  have h : deriv (g : ℝ → ℂ) = ((SchwartzMap.derivCLM ℂ ℂ g : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
    funext y; rw [SchwartzMap.derivCLM_apply]
  rw [h]; exact (SchwartzMap.derivCLM ℂ ℂ g).continuous

/-- **The fundamental gradient estimate.** `‖g x − g y‖² ≤ (x−y) ∫_y^x ‖g'‖²`. -/
