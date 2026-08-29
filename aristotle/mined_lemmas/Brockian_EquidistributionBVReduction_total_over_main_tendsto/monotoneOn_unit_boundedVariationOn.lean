import Mathlib

/-!
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian
namespace EquidistributionBVReduction

open Filter Finset

/-- The `N`-th equidistributed sample sum of `f`: the total of the values of `f` at the
`N` equidistributed sample points `0/N, 1/N, …, (N-1)/N` of the unit interval. -/

lemma monotoneOn_unit_boundedVariationOn {f : ℝ → ℝ}
    (hf : MonotoneOn f (Set.Icc (0:ℝ) 1)) : BoundedVariationOn f (Set.Icc (0:ℝ) 1) := by
  have h := hf.eVariationOn_le (Set.left_mem_Icc.2 zero_le_one)
    (Set.right_mem_Icc.2 zero_le_one)
  rw [Set.inter_self] at h
  exact (h.trans_lt ENNReal.ofReal_lt_top).ne

/-- Sanity check: the hypotheses of `total_over_main_tendsto` are satisfiable, e.g. by the
identity function on `[0,1]`. -/
example : Tendsto (fun N : ℕ => total (fun x => x) N / main (fun x => x) N) atTop (nhds 1) := by
  refine total_over_main_tendsto (monotoneOn_unit_boundedVariationOn ?_) ?_
  · exact fun a _ b _ hab => hab
  · rw [integral_id]
    norm_num

end EquidistributionBVReduction
end Brockian

