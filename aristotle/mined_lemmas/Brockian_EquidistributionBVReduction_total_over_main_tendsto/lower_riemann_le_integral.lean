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

lemma lower_riemann_le_integral (hf : MonotoneOn f (Set.Icc (0:ℝ) 1)) {m : ℕ} (hm : 0 < m) :
    ∑ k ∈ Finset.range m, f (k / m) * (1 / m) ≤ ∫ t in (0:ℝ)..1, f t := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hint : ∀ k < m, IntervalIntegrable f volume ((fun j : ℕ => (j : ℝ) / m) k)
      ((fun j : ℕ => (j : ℝ) / m) (k + 1)) := by
    intro k hk
    have := partition_integrable hf m hm hk
    simpa using this
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  simp only [Nat.cast_zero, zero_div] at hsum
  rw [div_self (ne_of_gt hm')] at hsum
  rw [← hsum]
  refine Finset.sum_le_sum ?_
  intro k hk
  have hk' : k < m := Finset.mem_range.mp hk
  have hcast : (((k : ℕ) + 1 : ℕ) : ℝ) / m = ((k : ℝ) + 1) / m := by push_cast; ring
  have hle : (k : ℝ) / m ≤ ((k : ℝ) + 1) / m := by gcongr; linarith
  have hlen : ((k : ℝ) + 1) / m - (k : ℝ) / m = 1 / m := by
    field_simp
    ring
  have hconst : f ((k : ℝ) / m) * (1 / m)
      = ∫ _t in ((k : ℝ) / m)..(((k : ℝ) + 1) / m), f ((k : ℝ) / m) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, hlen, mul_comm]
  simp only [hcast]
  rw [hconst]
  refine intervalIntegral.integral_mono_on hle intervalIntegrable_const
    (partition_integrable hf m hm hk') ?_
  intro t ht
  have h1 := partition_mem m hm hk'.le
  have h2 : (((k : ℕ) + 1 : ℕ) : ℝ) / m ∈ Set.Icc (0:ℝ) 1 := partition_mem m hm hk'
  push_cast at h2
  exact hf h1 ⟨le_trans h1.1 ht.1, le_trans ht.2 h2.2⟩ ht.1

