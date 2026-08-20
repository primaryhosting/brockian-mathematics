import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Brockian.EquidistributionBVReduction

/-!
# Existence of an equidistributed sequence

This file exhibits an explicit sequence which is equidistributed mod one in the sense of
`Brockian.EquidistributionBVReduction.Equidistributed`, so that the hypotheses of
`Brockian.EquidistributionBVReduction.configCount_density_of_BV` are satisfiable.

The sequence is the concatenation of the uniform grids of odd sizes: the `k`-th block consists
of the `2k+1` points `0/(2k+1), 1/(2k+1), …, 2k/(2k+1)`, and it occupies the indices
`k² ≤ n < (k+1)²`.  Since `Nat.sqrt n = k` exactly on that range of indices, the sequence has the
closed form `gridSeq n = (n - (sqrt n)²) / (2 * sqrt n + 1)`.
-/

open scoped BigOperators
open scoped Classical
open Filter Set

namespace Brockian
namespace EquidistributionBVReduction

/-- The concatenation of the uniform grids of odd sizes: the block of indices
`k² ≤ n < (k+1)²` runs through the `2k+1` points `j / (2k+1)`. -/

theorem configCount_density_of_BV {x : ℕ → ℝ} {w : ℝ → ℝ}
    (hx : Equidistributed x) (hw : BoundedVariationOn w (Set.Icc 0 1)) :
    Tendsto (fun N : ℕ => configCount w x N / N) atTop (nhds (∫ t in (0:ℝ)..1, w t)) := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    hw.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have hpi : IntervalIntegrable p volume 0 1 := by
    apply MonotoneOn.intervalIntegrable
    rwa [Set.uIcc_of_le (zero_le_one' ℝ)]
  have hqi : IntervalIntegrable q volume 0 1 := by
    apply MonotoneOn.intervalIntegrable
    rwa [Set.uIcc_of_le (zero_le_one' ℝ)]
  have hI : (∫ t in (0:ℝ)..1, w t)
      = (∫ t in (0:ℝ)..1, p t) - (∫ t in (0:ℝ)..1, q t) := by
    rw [← intervalIntegral.integral_sub hpi hqi]
    exact intervalIntegral.integral_congr (fun t _ => by rw [hpq]; rfl)
  have hcc : ∀ N : ℕ, configCount w x N / N
      = configCount p x N / N - configCount q x N / N := by
    intro N
    rw [← sub_div]
    congr 1
    simp only [configCount, hpq, Pi.sub_apply, Finset.sum_sub_distrib]
  simp only [hcc, hI]
  exact (configCount_density_of_monotoneOn hx hp).sub (configCount_density_of_monotoneOn hx hq)

end EquidistributionBVReduction
end Brockian

