import Mathlib
open Filter Topology
namespace MS2.Analysis2


theorem geometric_sum (r : ℝ) (hr : |r| < 1) : Tendsto (fun n => ∑ i ∈ Finset.range n, r^i) atTop (nhds (1/(1-r))) := by
  have h := (hasSum_geometric_of_abs_lt_one hr).tendsto_sum_nat
  simpa [one_div] using h

