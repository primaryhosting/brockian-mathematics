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

lemma sum_fiber_split (hx : ∀ n, x n ∈ Set.Ico (0:ℝ) 1) {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∑ k ∈ Finset.range m, ∑ n ∈ (Finset.range N).filter
        (fun n => (k / m : ℝ) ≤ x n ∧ x n < ((k : ℝ) + 1) / m), f (x n)
      = ∑ n ∈ Finset.range N, f (x n) := by
  classical
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hmaps : ∀ n ∈ Finset.range N, ⌊x n * m⌋₊ ∈ Finset.range m := by
    intro n _
    have h0 : 0 ≤ x n * m := mul_nonneg (hx n).1 hm'.le
    have h1 : x n * m < m := by
      have := (hx n).2
      nlinarith
    exact Finset.mem_range.mpr ((Nat.floor_lt h0).mpr h1)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => f (x n))]
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  refine Finset.filter_congr ?_
  intro n _
  have h0 : 0 ≤ x n * m := mul_nonneg (hx n).1 hm'.le
  rw [Nat.floor_eq_iff h0, div_le_iff₀ hm', lt_div_iff₀ hm']

