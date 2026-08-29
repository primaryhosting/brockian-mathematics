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

theorem integrable_deriv_sq (g : SchwartzMap ℝ ℂ) :
    Integrable (fun x => ‖deriv (g : ℝ → ℂ) x‖ ^ 2) volume := by
  have hd : deriv (g : ℝ → ℂ) = ((SchwartzMap.derivCLM ℂ ℂ g : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
    funext y; rw [SchwartzMap.derivCLM_apply]
  have h := schwartz_norm_mul_integrable (SchwartzMap.derivCLM ℂ ℂ g)
    (SchwartzMap.derivCLM ℂ ℂ g)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  rw [hd]; ring

