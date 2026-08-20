import Mathlib
open MeasureTheory
namespace C3.Meas

theorem measure_mono {X : Type*} [MeasurableSpace X] (μ : Measure X) {s t : Set X} (h : s ⊆ t) : μ s ≤ μ t :=
  MeasureTheory.measure_mono h
