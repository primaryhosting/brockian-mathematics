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

/-
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Filter Topology Set

namespace Brockian.EquidistributionBVReduction

open scoped Classical in
/-- `configCount x A N` is the number of indices `n < N` whose orbit point `x n`,
reduced mod `1`, lands in the configuration set `A`. -/

theorem tendsto_average_of_BV (hx : EquidistributedMod1 x)
    (hf : BoundedVariationOn f (Set.Icc (0:ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N)
      atTop (𝓝 (∫ t in (0:ℝ)..1, f t)) := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have hip : IntervalIntegrable p volume 0 1 := by
    apply MonotoneOn.intervalIntegrable
    rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hiq : IntervalIntegrable q volume 0 1 := by
    apply MonotoneOn.intervalIntegrable
    rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hsplit : (∫ t in (0:ℝ)..1, f t) = (∫ t in (0:ℝ)..1, p t) - ∫ t in (0:ℝ)..1, q t := by
    rw [← intervalIntegral.integral_sub hip hiq, hpq]
    simp [Pi.sub_apply]
  rw [hsplit]
  have hP := tendsto_average_of_monotoneOn hx hp
  have hQ := tendsto_average_of_monotoneOn hx hq
  refine (hP.sub hQ).congr ?_
  intro N
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [hpq]
  simp

/-- **Configuration count density from bounded variation.**  If the indicator function of a
configuration set `A` has bounded variation on `[0,1]`, then along any sequence that is
equidistributed mod `1` the configuration counts have a density, equal to the integral of the
indicator over `[0,1]`. -/
