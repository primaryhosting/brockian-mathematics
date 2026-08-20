import Mathlib
open MeasureTheory
namespace C3.Meas

theorem measure_union_le {X : Type*} [MeasurableSpace X] (μ : Measure X) (s t : Set X) : μ (s ∪ t) ≤ μ s + μ t :=
  MeasureTheory.measure_union_le s t
