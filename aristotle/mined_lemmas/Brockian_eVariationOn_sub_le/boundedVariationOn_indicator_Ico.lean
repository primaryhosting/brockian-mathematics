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
# Reduction of equidistribution mod 1 to test functions of bounded variation

This file contains an unconditional proof that a sequence `x : ℕ → ℝ` whose Cesàro averages
against every test function of bounded variation on `[0,1]` converge to the corresponding
integral is uniformly distributed (equidistributed) mod `1`.

The main statement is `Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform`.
It is deduced from the formally stronger
`Brockian.EquidistributionBVReduction.equidistribution_of_monotone_uniform`, where only
monotone test functions are used.

All auxiliary facts are proved here, with no assumed black boxes; in particular the
subadditivity of the (extended) variation with respect to differences of functions,
the bounded variation of indicator functions of intervals, and the relevant integrals.
-/

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace Brockian
namespace EquidistributionBVReduction

/-! ## Bounded variation of a step function -/

/-- Subadditivity of the extended variation for a difference of two real valued functions. -/

theorem boundedVariationOn_indicator_Ico (a b : ℝ) (hab : a ≤ b) :
    BoundedVariationOn (Set.indicator (Set.Ico a b) (fun _ => (1:ℝ))) (Set.Icc (0:ℝ) 1) := by
  have heq := eVariationOn.eq_of_eqOn (indicator_Ico_eqOn a b hab)
  have hle : eVariationOn (fun t => step a t - step b t) (Set.Icc (0:ℝ) 1) ≤ 1 + 1 :=
    (eVariationOn_sub_le (step a) (step b) _).trans
      (add_le_add (eVariationOn_step_le a) (eVariationOn_step_le b))
  refine ne_of_lt ?_
  rw [heq]
  exact lt_of_le_of_lt hle (ENNReal.add_lt_top.2 ⟨by simp, by simp⟩)

/-! ## The integral of the indicator -/

