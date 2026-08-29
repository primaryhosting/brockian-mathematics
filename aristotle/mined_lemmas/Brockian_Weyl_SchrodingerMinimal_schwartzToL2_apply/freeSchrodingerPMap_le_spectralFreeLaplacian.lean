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

theorem freeSchrodingerPMap_le_spectralFreeLaplacian :
    freeSchrodingerPMap ≤ spectralFreeLaplacian := by
  have hdom : ∀ f : SchwartzMap ℝ ℂ,
      schwartzToL2 f ∈ spectralFreeLaplacian.domain := by
    intro f
    rw [spectralFreeLaplacian, conjugatePMap_domain]
    exact ⟨schwartzToL2 (fourierSchwartz f),
      schwartzToL2_mem_freeSymbolMaximal_domain (fourierSchwartz f),
      fourierL2_symm_schwartzToL2 f⟩
  refine ⟨?_, ?_⟩
  · rw [freeSchrodingerPMap_domain]
    rintro u ⟨f, rfl⟩
    exact hdom f
  · rintro x y hxy
    obtain ⟨f, hf⟩ := (LinearMap.mem_range).mp x.2
    have hxe : x = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f :=
      Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hf.symm)
    have hyv : (y : L2R) = Brockian.FreeLaplacianPlancherel.fourierL2.symm
        (schwartzToL2 (fourierSchwartz f)) := by
      rw [fourierL2_symm_schwartzToL2 f, hf, hxy]
    let v : freeSymbolMaximal.domain :=
      ⟨schwartzToL2 (fourierSchwartz f),
        schwartzToL2_mem_freeSymbolMaximal_domain (fourierSchwartz f)⟩
    have hvy : spectralFreeLaplacian y
        = Brockian.FreeLaplacianPlancherel.fourierL2.symm (freeSymbolMaximal v) :=
      conjugatePMap_apply_of_coe _ _ v y hyv
    rw [hxe, freeSchrodingerPMap_toFun_ofInjective, freeCoreMap_apply, hvy,
      freeSymbolMaximal_apply_fourierSchwartz f v rfl, map_neg,
      fourierL2_symm_schwartzToL2 (D2 f)]

end Brockian.Weyl.FreeLaplacianCorrected

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

