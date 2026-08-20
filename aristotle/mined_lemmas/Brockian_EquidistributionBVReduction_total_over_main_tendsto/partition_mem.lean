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

private lemma partition_mem (m : ℕ) (hm : 0 < m) {k : ℕ} (hk : k ≤ m) :
    ((k : ℝ) / m) ∈ Set.Icc (0:ℝ) 1 := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hm']
  exact_mod_cast hk

