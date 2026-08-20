import Mathlib
open intervalIntegral MeasureTheory
namespace C2.An4

/-- Fundamental theorem of calculus: if `F` has derivative `f` everywhere and `f` is
continuous, then `∫ x in a..b, f x = F b - F a`. -/

theorem geom_series_sum (r : ℝ) (hr : |r| < 1) :
    Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, r ^ i) Filter.atTop (nhds (1 / (1 - r))) := by
  rw [one_div]
  exact (hasSum_geometric_of_abs_lt_one hr).tendsto_sum_nat

/-- A function continuous on the compact interval `[a, b]` is uniformly continuous there. -/
