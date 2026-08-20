import Mathlib
open MeasureTheory
namespace C3.Meas

theorem integral_nonneg {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ ∫ x, f x ∂μ :=
  MeasureTheory.integral_nonneg hf
end C3.Meas

