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

private theorem fourierL2_schwartzToL2 (f : SchwartzMap ℝ ℂ) :
    Brockian.FreeLaplacianPlancherel.fourierL2 (schwartzToL2 f)
      = schwartzToL2 (fourierSchwartz f) := by
  show MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (schwartzToL2 f) = _
  rw [schwartzToL2_apply, schwartzToL2_apply, fourierSchwartz,
    SchwartzMap.fourierTransformCLM_apply]
  exact SchwartzMap.toLp_fourier_eq f

