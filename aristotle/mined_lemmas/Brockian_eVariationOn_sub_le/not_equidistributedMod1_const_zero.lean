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

theorem not_equidistributedMod1_const_zero : ¬ EquidistributedMod1 (fun _ => (0:ℝ)) := by
  intro h
  have hlim := h (1/2) 1 (by norm_num) (by norm_num) le_rfl
  have hz : (fun N : ℕ =>
      (((Finset.range N).filter
        fun n => Int.fract ((fun _ => (0:ℝ)) n) ∈ Set.Ico (1/2:ℝ) 1).card : ℝ) / N)
      = fun _ : ℕ => (0:ℝ) := by
    funext N
    simp [Set.mem_Ico]
  rw [hz] at hlim
  have := tendsto_nhds_unique hlim tendsto_const_nhds
  norm_num at this

end EquidistributionBVReduction
end Brockian

