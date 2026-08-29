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

theorem coeFn_schwartzToL2 (a : SchwartzMap ℝ ℂ) :
    (schwartzToL2 a : ℝ → ℂ) =ᵐ[volume] a := by
  rw [schwartzToL2_apply]
  exact a.coeFn_toLp 2 (volume : Measure ℝ)

