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

theorem freeSchrodingerPMap_toFun_ofInjective (f : SchwartzMap ℝ ℂ) :
    freeSchrodingerPMap
        (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f)
      = freeCoreMap f := by
  show freeCoreMap.comp
      (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective).symm.toLinearMap
      (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f)
    = freeCoreMap f
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]

end Brockian.Weyl.SchrodingerGate1Final

/-! ## From `Brockian/WeylMaximalMultiplication.lean` -/

namespace Brockian.Weyl.MaximalMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

