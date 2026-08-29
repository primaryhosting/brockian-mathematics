import Brockian.EquidistributionBVReduction

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
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Filter Topology
open scoped BigOperators Classical

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` lies in `[a, b)`. -/

lemma sum_le_total (hg : Monotone g) (hm : 0 < m) :
    ∑ i ∈ Finset.range m,
        g ((i : ℝ) / m) * (countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ)
      ≤ total g x N := by
  have step : ∀ i ∈ Finset.range m,
      g ((i : ℝ) / m) * (countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ)
        = ∑ n ∈ Finset.range N,
            (if Int.fract (x n) ∈ Set.Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then g ((i:ℝ)/m) else 0) := by
    intro i _
    rw [countIco_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split <;> ring
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  refine Finset.sum_le_sum fun n _ => ?_
  set y := Int.fract (x n) with hy
  have hy0 : 0 ≤ y := Int.fract_nonneg _
  have hy1 : y < 1 := Int.fract_lt_one _
  have hbound : ∀ i ∈ Finset.range m,
      (if y ∈ Set.Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then g ((i:ℝ)/m) else 0)
        ≤ g y * (if y ∈ Set.Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then (1:ℝ) else 0) := by
    intro i _
    by_cases h : y ∈ Set.Ico ((i:ℝ)/m) (((i:ℝ)+1)/m)
    · simp [h, hg h.1]
    · simp [h]
  calc ∑ i ∈ Finset.range m,
        (if y ∈ Set.Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then g ((i:ℝ)/m) else 0)
      ≤ ∑ i ∈ Finset.range m, g y * (if y ∈ Set.Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then (1:ℝ) else 0) :=
        Finset.sum_le_sum hbound
    _ = g y := by rw [← Finset.mul_sum, sum_indicator_eq_one hm hy0 hy1, mul_one]

/-- Upper step-function bound for the total sum. -/
