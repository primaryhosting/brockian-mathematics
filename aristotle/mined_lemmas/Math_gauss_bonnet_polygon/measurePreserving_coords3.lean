import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma measurePreserving_coords3 : MeasurePreserving coords3 volume volume := by
  have h1 : MeasurePreserving (Prod.swap : (ℝ × ℝ) × ℝ → ℝ × (ℝ × ℝ)) volume volume :=
    ⟨measurable_swap, Measure.prod_swap⟩
  have h2 : MeasurePreserving
      (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow.symm : (ℝ × ℝ) → (Fin 2 → ℝ)))
      volume volume :=
    MeasurePreserving.prod (MeasurePreserving.id _) (volume_preserving_finTwoArrow ℝ).symm
  have h3 : MeasurePreserving
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm) volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm
  have hcomp := (h3.comp h2).comp h1
  convert hcomp using 1
  funext q
  obtain ⟨⟨x, y⟩, t⟩ := q
  funext i
  fin_cases i <;>
    simp [coords3, MeasurableEquiv.piFinSuccAbove, Fin.insertNth, Fin.succAboveCases,
      MeasurableEquiv.finTwoArrow]

/-- Fubini in the last coordinate: the volume of a region of the unit ball lying over a
planar region `D`. -/
