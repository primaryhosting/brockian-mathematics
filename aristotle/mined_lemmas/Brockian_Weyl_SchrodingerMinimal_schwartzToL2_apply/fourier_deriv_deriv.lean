/-
  Corpus declarations (reproduced verbatim from the Brockian modules, restricted to
  what is needed) together with the new bridge theorem

      freeSchrodingerPMap ≤ spectralFreeLaplacian.
-/
import Mathlib

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace ENNReal

/-! ## From `Brockian/WeylSchrodingerMinimal.lean` -/

namespace Brockian.Weyl.SchrodingerMinimal

/-- L² space for the one-dimensional Schrödinger operator. -/
noncomputable abbrev H2 := Lp ℂ 2 (volume : Measure ℝ)

/-- **The Schwartz core, embedded in `L²`.** -/

private theorem fourier_deriv_deriv (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    𝓕 (deriv (deriv ⇑f)) x = -(4 * (Real.pi : ℂ) ^ 2 * (x : ℂ) ^ 2) * 𝓕 (⇑f) x := by
  have hc : (⇑(SchwartzMap.derivCLM ℂ ℂ f) : ℝ → ℂ) = deriv (⇑f) :=
    funext fun y => SchwartzMap.derivCLM_apply ℂ f y
  have hc2 : (⇑(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)) : ℝ → ℂ)
      = deriv (deriv (⇑f)) := by
    rw [funext fun y => SchwartzMap.derivCLM_apply ℂ (SchwartzMap.derivCLM ℂ ℂ f) y, hc]
  have hi1 : Integrable (deriv ⇑f) volume := by
    simpa [hc] using (SchwartzMap.derivCLM ℂ ℂ f).integrable (μ := volume)
  have hi2 : Integrable (deriv (deriv ⇑f)) volume := by
    simpa [hc2] using
      (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)).integrable (μ := volume)
  have hd1 : Differentiable ℝ (deriv ⇑f) := by
    simpa [hc] using (SchwartzMap.derivCLM ℂ ℂ f).differentiable
  rw [Real.fourier_deriv hi1 hd1 hi2, Real.fourier_deriv f.integrable f.differentiable hi1]
  simp only [smul_eq_mul]
  linear_combination (4 * (Real.pi : ℂ) ^ 2 * (x : ℂ) ^ 2 * 𝓕 (⇑f) x) * Complex.I_sq

/-- Pointwise: the free symbol times `𝓕 f` is `-𝓕 (f'')`. -/
