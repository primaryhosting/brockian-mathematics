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

theorem integral_conj_mul_deriv (u v : SchwartzMap ℝ ℂ) :
    ∫ x : ℝ, conj (u x) * deriv (v : ℝ → ℂ) x
      = -∫ x : ℝ, conj (deriv (u : ℝ → ℂ) x) * v x := by
  have hu : ∀ x : ℝ, HasDerivAt (fun y => conj (u y)) (conj (deriv (u : ℝ → ℂ) x)) x := by
    intro x
    have h := (u.differentiable.differentiableAt (x := x)).hasDerivAt
    simpa using h.star
  have hv : ∀ x : ℝ, HasDerivAt (v : ℝ → ℂ) (deriv (v : ℝ → ℂ) x) x :=
    fun x => (v.differentiable.differentiableAt (x := x)).hasDerivAt
  have hdv : (deriv (v : ℝ → ℂ)) = ((SchwartzMap.derivCLM ℂ ℂ v : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
    funext x; rw [SchwartzMap.derivCLM_apply]
  have hdu : (deriv (u : ℝ → ℂ)) = ((SchwartzMap.derivCLM ℂ ℂ u : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
    funext x; rw [SchwartzMap.derivCLM_apply]
  have h1 : Integrable ((fun x => conj (u x)) * deriv (v : ℝ → ℂ)) volume := by
    rw [hdv]; exact integrable_conj_mul u (SchwartzMap.derivCLM ℂ ℂ v)
  have h2 : Integrable ((fun x => conj (deriv (u : ℝ → ℂ) x)) * (v : ℝ → ℂ)) volume := by
    rw [hdu]; exact integrable_conj_mul (SchwartzMap.derivCLM ℂ ℂ u) v
  have h3 : Integrable ((fun x => conj (u x)) * (v : ℝ → ℂ)) volume := integrable_conj_mul u v
  exact MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable hu hv h1 h2 h3

/-- The second derivative as a continuous linear map on the Schwartz space. -/
