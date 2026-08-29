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

theorem D2_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) : D2 f x = deriv (deriv f) x := by
  have hc : (⇑(SchwartzMap.derivCLM ℂ ℂ f) : ℝ → ℂ) = deriv (⇑f) :=
    funext fun y => SchwartzMap.derivCLM_apply ℂ f y
  simp only [D2, ContinuousLinearMap.comp_apply, SchwartzMap.derivCLM_apply, hc]

end Brockian.Weyl.SchrodingerMinimal

/-! ## From `Brockian/WeylSchrodingerGate1Final.lean` -/

namespace Brockian.Weyl.SchrodingerGate1Final

open Brockian.Weyl.SchrodingerMinimal

noncomputable abbrev L2R := Brockian.Weyl.SchrodingerMinimal.H2

/-- The free kinetic action `f |-> -f''` on Schwartz functions, valued in L2. -/
