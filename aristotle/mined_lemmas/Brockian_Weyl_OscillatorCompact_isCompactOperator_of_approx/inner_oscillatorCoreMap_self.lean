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

theorem inner_oscillatorCoreMap_self (g : SchwartzMap ℝ ℂ) :
    inner ℂ (oscillatorCoreMap g) (schwartzToL2 g) = (energy g : ℂ) := by
  rw [oscillatorCoreMap_expanded, inner_add_left, inner_neg_left, inner_toLp, inner_toLp]
  have hdg : ((SchwartzMap.derivCLM ℂ ℂ g : SchwartzMap ℝ ℂ) : ℝ → ℂ) = deriv (g : ℝ → ℂ) := by
    funext y; rw [SchwartzMap.derivCLM_apply]
  -- the kinetic term
  have hkin := integral_conj_mul_deriv (SchwartzMap.derivCLM ℂ ℂ g) g
  rw [hdg] at hkin
  have hkin2 : -∫ x : ℝ, conj (D2 g x) * g x
      = ((∫ x : ℝ, ‖deriv (g : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    have hD2 : ∫ x : ℝ, conj (D2 g x) * g x
        = ∫ x : ℝ, conj (deriv (deriv (g : ℝ → ℂ)) x) * g x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [D2_apply]
    rw [hD2, ← hkin, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact conj_mul_self _
  -- the potential term
  have hpot : ∫ x : ℝ, conj (quadraticMulSchwartz g x) * g x
      = ((∫ x : ℝ, x ^ 2 * ‖g x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [quadraticMulSchwartz_apply]
    rw [map_mul, map_pow, Complex.conj_ofReal, mul_assoc, conj_mul_self]
    push_cast
    ring
  rw [hpot, energy]
  push_cast
  rw [hkin2]

/-! ### The set of Schwartz states of bounded energy -/

/-- The approximation property passes to the closure. -/
