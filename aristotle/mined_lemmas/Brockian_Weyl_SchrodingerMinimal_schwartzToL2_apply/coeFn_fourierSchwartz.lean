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

private theorem coeFn_fourierSchwartz (f : SchwartzMap ℝ ℂ) :
    (⇑(fourierSchwartz f) : ℝ → ℂ) = 𝓕 (⇑f) := by
  rw [fourierSchwartz, SchwartzMap.fourierTransformCLM_apply]
  exact SchwartzMap.fourier_coe f

open FourierTransform in
/-- The Fourier transform of the second derivative of a Schwartz function is
multiplication by `-(4 π² ξ²)`. -/
