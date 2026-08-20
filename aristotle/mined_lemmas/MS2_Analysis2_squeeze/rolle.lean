import Mathlib
open Filter Topology
namespace MS2.Analysis2


theorem rolle (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hc : ContinuousOn f (Set.Icc a b))
    (hd : DifferentiableOn ℝ f (Set.Ioo a b)) (he : f a = f b) : ∃ c ∈ Set.Ioo a b, deriv f c = 0 :=
  exists_deriv_eq_zero hab hc he

