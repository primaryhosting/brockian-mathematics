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

lemma tendsto_sum_div_monotone (hp : MonotoneOn p (Set.Icc (0:ℝ) 1)) :
    Tendsto (fun N : ℕ => total p N / N) atTop (nhds (∫ x in (0:ℝ)..1, p x)) := by
  have hbound : ∀ᶠ N : ℕ in atTop,
      |total p N / N - ∫ x in (0:ℝ)..1, p x| ≤ |p 1 - p 0| / N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have h1 := sum_div_le_integral hp hN
    have h2 := integral_sub_sum_div_le hp hN
    have hN' : (0:ℝ) < N := by exact_mod_cast hN
    rw [abs_le]
    constructor
    · have : (p 1 - p 0) / N ≤ |p 1 - p 0| / N := by
        gcongr
        exact le_abs_self _
      linarith
    · have : (0:ℝ) ≤ |p 1 - p 0| / N := by positivity
      linarith
  have hzero : Tendsto (fun N : ℕ => |p 1 - p 0| / N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => dist_nonneg) ?_ hzero
  filter_upwards [hbound] with N hN using by rwa [Real.dist_eq]

end Monotone

/-- **Equidistribution / bounded-variation reduction.**
For a function `f` of bounded variation on `[0,1]` whose mean value over `[0,1]` is nonzero,
the total `∑_{k<N} f (k/N)` of the values of `f` over the `N` equidistributed sample points
is asymptotic to the main term `N * ∫₀¹ f`, i.e. their ratio tends to `1`.

This is the unconditional form: no equidistribution hypothesis is assumed, it is proved here
for the uniform sample points via the bounded-variation (monotone difference) reduction. -/
