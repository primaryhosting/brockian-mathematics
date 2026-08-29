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
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Filter Finset

namespace Brockian.EquidistributionBVReduction

/-- The set of *configurations* of size `N` in the residue class `r` modulo `q`:
pairs `(a, b)` with `a, b < N` and `a + b ≡ r [MOD q]`. -/

lemma tendsto_sub_div (q : ℕ) : Tendsto (fun N : ℕ => ((N : ℝ) - q) / N) atTop (nhds 1) := by
  have h : ∀ᶠ N : ℕ in atTop, ((N : ℝ) - q) / N = 1 - (q : ℝ) / N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    field_simp
  rw [tendsto_congr' h]
  simpa using (tendsto_const_nhds (x := (1:ℝ)) (f := atTop (α := ℕ))).sub
    (tendsto_const_div_atTop_nhds_zero_nat (q : ℝ))

/-- The upper comparison sequence `(N + q) / N` tends to `1`. -/
