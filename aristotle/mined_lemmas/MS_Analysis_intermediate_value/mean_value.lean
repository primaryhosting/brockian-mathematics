import Mathlib
namespace MS.Analysis

theorem mean_value (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hc : ContinuousOn f (Set.Icc a b)) (hd : DifferentiableOn ℝ f (Set.Ioo a b)) :
    ∃ c ∈ Set.Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hc hd
