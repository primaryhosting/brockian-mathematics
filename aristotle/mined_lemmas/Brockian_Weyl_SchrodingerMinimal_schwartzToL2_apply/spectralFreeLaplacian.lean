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

noncomputable def spectralFreeLaplacian : L2R →ₗ.[Complex] L2R :=
  conjugatePMap Brockian.FreeLaplacianPlancherel.fourierL2.symm freeSymbolMaximal

/-! ### The bridge theorem -/

open FourierTransform in
/-- The Fourier transform of a Schwartz function, as a Schwartz function. -/
private noncomputable def fourierSchwartz (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.fourierTransformCLM ℂ f

open FourierTransform in
