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

@[simp] theorem D2_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    D2 f x = deriv (deriv (f : ℝ → ℂ)) x := by
  have hdf : ((SchwartzMap.derivCLM ℂ ℂ f : SchwartzMap ℝ ℂ) : ℝ → ℂ) = deriv (f : ℝ → ℂ) := by
    funext y; rw [SchwartzMap.derivCLM_apply]
  show (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)) x = _
  rw [SchwartzMap.derivCLM_apply, hdf]

/-- The kinetic term is symmetric on the Schwartz core. -/
