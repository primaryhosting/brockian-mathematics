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
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Classical

open Filter Finset

namespace Brockian.EquidistributionBVReduction

/-- The number of `n < N` lying in the residue class `r` modulo `q`. -/

theorem configCount_over_main_tendsto (q r s : ℕ) (hq : 0 < q) :
    Tendsto (fun N : ℕ => (configCount q r s N : ℝ) / mainTerm q N) atTop (nhds 1) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hprod := (tendsto_residueCount_div q r hq).mul (tendsto_residueCount_div q s hq)
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [configCount_eq_mul, mainTerm]
  push_cast
  field_simp

end Brockian.EquidistributionBVReduction

