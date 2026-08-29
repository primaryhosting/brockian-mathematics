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

theorem kinetic_symm (f g : SchwartzMap ℝ ℂ) :
    inner ℂ (schwartzToL2 (D2 f)) (schwartzToL2 g)
      = inner ℂ (schwartzToL2 f) (schwartzToL2 (D2 g)) := by
  rw [inner_toLp, inner_toLp]
  simp only [D2_apply]
  have hdf : ((SchwartzMap.derivCLM ℂ ℂ f : SchwartzMap ℝ ℂ) : ℝ → ℂ) = deriv (f : ℝ → ℂ) := by
    funext y; rw [SchwartzMap.derivCLM_apply]
  have hdg : ((SchwartzMap.derivCLM ℂ ℂ g : SchwartzMap ℝ ℂ) : ℝ → ℂ) = deriv (g : ℝ → ℂ) := by
    funext y; rw [SchwartzMap.derivCLM_apply]
  have h1 := integral_conj_mul_deriv (SchwartzMap.derivCLM ℂ ℂ f) g
  rw [hdf] at h1
  have h2 := integral_conj_mul_deriv f (SchwartzMap.derivCLM ℂ ℂ g)
  rw [hdg] at h2
  linear_combination h1 - h2

end Brockian.Weyl.SchrodingerMinimal

/-! ## Brockian/WeylHarmonicOscillator.lean -/

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace

namespace Brockian.Weyl.HarmonicOscillator

open Brockian.Weyl.Operator
open Brockian.Weyl.SchrodingerMinimal

noncomputable abbrev L2R := Brockian.Weyl.SchrodingerMinimal.H2

/-- Multiplication by `x^2` preserves Schwartz space. -/
