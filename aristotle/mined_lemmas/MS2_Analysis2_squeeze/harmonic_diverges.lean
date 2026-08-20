import Mathlib
open Filter Topology
namespace MS2.Analysis2


theorem harmonic_diverges : ¬ ∃ L, Tendsto (fun n => ∑ i ∈ Finset.range n, (1:ℝ)/(i+1)) atTop (nhds L) := by
  rintro ⟨L, hL⟩
  exact not_tendsto_nhds_of_tendsto_atTop Real.tendsto_sum_range_one_div_nat_succ_atTop L hL

end MS2.Analysis2

