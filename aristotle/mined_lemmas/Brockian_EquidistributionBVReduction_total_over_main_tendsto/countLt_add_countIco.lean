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

lemma countLt_add_countIco (hab : a ≤ b) :
    countLt x N a + countIco x N a b = countLt x N b := by
  classical
  have h1 : ((Finset.range N).filter (fun n => x n < b)).filter (fun n => x n < a)
      = (Finset.range N).filter (fun n => x n < a) := by
    ext n; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, lt_of_lt_of_le h.2 hab⟩, h.2⟩⟩
  have h2 : ((Finset.range N).filter (fun n => x n < b)).filter (fun n => ¬ (x n < a))
      = (Finset.range N).filter (fun n => a ≤ x n ∧ x n < b) := by
    ext n; simp only [Finset.mem_filter, Finset.mem_range, not_lt]
    tauto
  unfold countLt countIco
  rw [← h1, ← h2]
  exact Finset.card_filter_add_card_filter_not _

