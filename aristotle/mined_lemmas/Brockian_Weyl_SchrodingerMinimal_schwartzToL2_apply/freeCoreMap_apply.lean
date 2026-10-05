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

@[simp] theorem freeCoreMap_apply (f : SchwartzMap ℝ ℂ) :
    freeCoreMap f = -(schwartzToL2 (D2 f)) := by
  simp [freeCoreMap]

/-- The genuine minimal free Laplacian `-d^2/dx^2` on the Schwartz core. -/
