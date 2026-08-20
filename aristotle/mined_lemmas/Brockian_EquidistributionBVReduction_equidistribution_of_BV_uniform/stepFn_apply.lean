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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Set MeasureTheory
open scoped Topology BigOperators Classical

namespace Brockian.EquidistributionBVReduction

/-- The Cesàro average of `f` along the fractional parts of the sequence `u`. -/

lemma stepFn_apply {m : ℕ} (c : ℕ → ℝ) {x : ℝ} {j : ℕ} (hj : j < m)
    (hx : x ∈ Set.Ico ((j : ℝ) / m) (((j : ℝ) + 1) / m)) : stepFn m c x = c j := by
  have hm : (0 : ℝ) < m := by
    have : 0 < m := lt_of_le_of_lt (Nat.zero_le j) hj
    exact_mod_cast this
  unfold stepFn
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hj)]
  · rw [Set.indicator_of_mem hx]; ring
  · intro i _ hij
    have hnot : x ∉ Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m) := by
      rcases lt_or_gt_of_ne hij with h | h
      · have hij' : ((i : ℝ) + 1) ≤ (j : ℝ) := by exact_mod_cast h
        have hle : ((i : ℝ) + 1) / m ≤ (j : ℝ) / m := by gcongr
        intro hmem
        exact absurd (lt_of_lt_of_le hmem.2 (hle.trans hx.1)) (lt_irrefl _)
      · have hij' : ((j : ℝ) + 1) ≤ (i : ℝ) := by exact_mod_cast h
        have hle : ((j : ℝ) + 1) / m ≤ (i : ℝ) / m := by gcongr
        intro hmem
        exact absurd (lt_of_lt_of_le hx.2 (hle.trans hmem.1)) (lt_irrefl _)
    rw [Set.indicator_of_notMem hnot]; ring

