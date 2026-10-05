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

lemma boundedVariationOn_of_monotoneOn_Icc01 {f : ℝ → ℝ}
    (hf : MonotoneOn f (Set.Icc (0:ℝ) 1)) : BoundedVariationOn f (Set.Icc (0:ℝ) 1) := by
  have h := hf.eVariationOn_le (a := 0) (b := 1) (by norm_num) (by norm_num)
  rw [Set.inter_eq_left.2 (by norm_num)] at h
  exact (h.trans_lt ENNReal.ofReal_lt_top).ne

