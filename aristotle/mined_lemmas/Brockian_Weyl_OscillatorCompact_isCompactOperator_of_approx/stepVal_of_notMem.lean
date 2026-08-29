/-
  CompactCriterion.lean — an abstract compactness criterion: an operator whose
  unit-ball image is uniformly approximable by finite-dimensional subspaces is
  a compact operator.
-/
import Mathlib

open Metric Filter

namespace Brockian.Weyl.OscillatorCompact

/-- An operator whose closed-unit-ball image is uniformly approximable by
finite-dimensional subspaces is a compact operator. -/

theorem stepVal_of_notMem (c : ℕ → ℂ) {Rr hh : ℝ} (hh0 : 0 ≤ hh) {n : ℕ}
    {x : ℝ} (hx : x ∉ Set.Ioc (-Rr) (-Rr + n * hh)) : stepVal c Rr hh n x = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  refine Set.indicator_of_notMem (fun hxj => hx ?_) _
  rw [← cells_union Rr hh hh0 n]
  exact Set.mem_biUnion hj hxj

/-- The `L²` class of the indicator of the `j`-th cell. -/
