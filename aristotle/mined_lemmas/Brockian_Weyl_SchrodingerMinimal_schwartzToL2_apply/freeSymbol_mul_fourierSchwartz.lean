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

private theorem freeSymbol_mul_fourierSchwartz (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    freeSymbol x * fourierSchwartz f x = -(fourierSchwartz (D2 f) x) := by
  have hD2 : (⇑(D2 f) : ℝ → ℂ) = deriv (deriv (⇑f)) := funext fun y => D2_apply f y
  rw [coeFn_fourierSchwartz, coeFn_fourierSchwartz, hD2, fourier_deriv_deriv f x, freeSymbol]
  push_cast
  ring

/-- The `L²` Fourier transform sends the class of a Schwartz function to the class of its
Fourier transform (Plancherel's unitary agrees with the Schwartz Fourier transform). -/
