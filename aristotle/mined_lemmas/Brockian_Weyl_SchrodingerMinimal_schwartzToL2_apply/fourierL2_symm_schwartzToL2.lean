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

private theorem fourierL2_symm_schwartzToL2 (f : SchwartzMap ℝ ℂ) :
    Brockian.FreeLaplacianPlancherel.fourierL2.symm (schwartzToL2 (fourierSchwartz f))
      = schwartzToL2 f := by
  rw [← fourierL2_schwartzToL2 f, LinearIsometryEquiv.symm_apply_apply]

/-- Value of a conjugated operator at an element of its domain, described by its
underlying vector. -/
