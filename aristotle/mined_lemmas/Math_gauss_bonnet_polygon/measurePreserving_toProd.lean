import RequestProject.Sector

/-!
# Volume of a wedge in three-dimensional space

The main result of this file is `SphericalArea.volume_wedge`: for a unit vector `u` and two
linearly independent vectors `s`, `t` orthogonal to `u`, the set of points of the open unit ball
whose orthogonal projection to `u^⊥` lies in the double wedge spanned by `s` and `t` has volume
`4 * angle s t / 3`.
-/

open MeasureTheory Real Set Metric InnerProductGeometry
open scoped ENNReal Real RealInnerProductSpace

namespace SphericalArea

/-- Coordinates of `EuclideanSpace ℝ (Fin 3)` as a product `ℝ × (ℝ × ℝ)`. -/

lemma measurePreserving_toProd : MeasurePreserving toProd volume volume := by
  have e1 : MeasurePreserving (@WithLp.ofLp 2 (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_ofLp _
  have e2 := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
  have e3 : MeasurePreserving
      (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow (α := ℝ))) volume volume :=
    (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)
  convert (e3.comp (e2.comp e1)) using 1

