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

import Mathlib

/-!
# Reduction of equidistribution statements to functions of bounded variation

This file develops the classical "bounded variation reduction" step in equidistribution
theory: if a sequence `x : ℕ → ℝ` taking values in `[0, 1)` is equidistributed (i.e. the
proportion of the first `N` terms lying below `c` tends to `c` for every `c ∈ [0,1]`), then
for every function `f` of bounded variation on `[0,1]` the averages
`(1/N) * ∑_{n < N} f (x n)` converge to `∫₀¹ f`.

The final statement `total_over_main_tendsto` says that the *total* sum `∑_{n < N} f (x n)`
divided by the *main term* `N * ∫₀¹ f` tends to `1`, whenever the integral is nonzero.
-/

open Filter Finset MeasureTheory
open scoped Topology

namespace Brockian.EquidistributionBVReduction

/-- The number of indices `n < N` with `x n < c`. -/

theorem bv_average_tendsto (hf : BoundedVariationOn f (Set.Icc (0:ℝ) 1))
    (hx : ∀ n, x n ∈ Set.Ico (0:ℝ) 1) (heq : Equidistributed x) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (x n)) / N) atTop
      (𝓝 (∫ t in (0:ℝ)..1, f t)) := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have huicc : Set.uIcc (0:ℝ) 1 = Set.Icc (0:ℝ) 1 := Set.uIcc_of_le zero_le_one
  have hpi : IntervalIntegrable p volume 0 1 :=
    MonotoneOn.intervalIntegrable (by rw [huicc]; exact hp)
  have hqi : IntervalIntegrable q volume 0 1 :=
    MonotoneOn.intervalIntegrable (by rw [huicc]; exact hq)
  have hInt : (∫ t in (0:ℝ)..1, f t)
      = (∫ t in (0:ℝ)..1, p t) - ∫ t in (0:ℝ)..1, q t := by
    rw [hpq]
    simpa using intervalIntegral.integral_sub hpi hqi
  have hlim := (monotone_average_tendsto hp hx heq).sub (monotone_average_tendsto hq hx heq)
  rw [← hInt] at hlim
  refine hlim.congr fun N => ?_
  rw [hpq]
  simp [Finset.sum_sub_distrib, sub_div]

/-- The total sum `∑_{n < N} f (x n)` is asymptotic to the main term `N * ∫₀¹ f`.

This is unconditional: the bounded-variation reduction it relies on (`bv_average_tendsto`)
is proved in this file, not assumed. -/
