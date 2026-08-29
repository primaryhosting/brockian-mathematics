/-
Volume of a wedge of the unit ball of `EuclideanSpace ℝ (Fin 3)` in standard position.

This is an auxiliary file for the Gauss-Bonnet (Girard) theorem for spherical triangles.
-/
import RequestProject.Sector

open MeasureTheory Metric Set Real
open scoped ENNReal

namespace Math

/-- Euclidean 3-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The wedge of the unit ball cut out by the half-spaces with inner normals
`(1,0,0)` and `(cos t, sin t, 0)`. -/

theorem volume_wedgeStd (t : ℝ) (ht0 : 0 ≤ t) (htpi : t ≤ π) :
    volume (wedgeStd t) = ENNReal.ofReal (2 * (π - t) / 3) := by
  have step1 : volume (wedgeStd t) = volume (wedgePi t) := by
    rw [← toLp_preimage_wedgeStd t,
      (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage (measurableSet_wedgeStd t).nullMeasurableSet]
  have step2 : volume (wedgePi t) = volume (wedgeProd t) := by
    have hpre : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2) ⁻¹' (wedgeProd t)
        = wedgePi t := rfl
    rw [← hpre, (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).measure_preimage]
    have : wedgeProd t = (Prod.map id (MeasurableEquiv.finTwoArrow (α := ℝ))) ⁻¹' (wedgeProd2 t) :=
      (prodMap_preimage_wedgeProd2 t).symm
    rw [this]
    exact (((measurableSet_wedgeProd2 t).preimage (by fun_prop))).nullMeasurableSet
  have step3 : volume (wedgeProd t) = volume (wedgeProd2 t) := by
    have hmp : MeasurePreserving (Prod.map id (MeasurableEquiv.finTwoArrow (α := ℝ)))
        (volume : Measure (ℝ × (Fin 2 → ℝ))) (volume : Measure (ℝ × (ℝ × ℝ))) := by
      rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
      exact (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)
    rw [← prodMap_preimage_wedgeProd2 t]
    exact hmp.measure_preimage (measurableSet_wedgeProd2 t).nullMeasurableSet
  have step4 : volume (wedgeProd2 t)
      = ∫⁻ z : ℝ, volume (planeSector t (Real.sqrt (1 - z ^ 2))) := by
    rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_wedgeProd2 t)]
    exact lintegral_congr fun z => by rw [slice_wedgeProd2 t z]
  rw [step1, step2, step3, step4]
  have hcoef : (0 : ℝ) ≤ (π - t) / 2 := by linarith
  have : ∀ z : ℝ, volume (planeSector t (Real.sqrt (1 - z ^ 2)))
      = ENNReal.ofReal ((π - t) / 2 * (Real.sqrt (1 - z ^ 2)) ^ 2) := fun z =>
    volume_planeSector t ht0 htpi _ (Real.sqrt_nonneg _)
  simp_rw [this]
  rw [lintegral_slice ((π - t) / 2) hcoef]
  congr 1
  ring

end Math

/-
Area of a circular sector of the plane, computed via polar coordinates.

This is an auxiliary file for the Gauss-Bonnet (Girard) theorem for spherical triangles.
-/
import Mathlib

open MeasureTheory Metric Set Real
open scoped ENNReal

namespace Math

/-- The set of points of the disc of radius `R` lying in the intersection of the two half-planes
`{w | 0 < w.1}` and `{w | 0 < ⟪w, (cos t, sin t)⟫}`.  For `0 ≤ t ≤ π` this is a circular
sector of angle `π - t`. -/
