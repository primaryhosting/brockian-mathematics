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

lemma stepFn_lower_le {f : ℝ → ℝ} (hf : MonotoneOn f (Set.Icc 0 1)) {m : ℕ} (hm : 0 < m)
    {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    stepFn m (fun i => f ((i : ℝ) / m)) x ≤ f x := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨j, hj, hxj⟩ := exists_mem_partition hm hx
  rw [stepFn_apply _ hj hxj]
  have h0 : (0 : ℝ) ≤ (j : ℝ) / m := by positivity
  have h1 : (j : ℝ) / m ≤ 1 := by
    rw [div_le_one hm']
    exact_mod_cast hj.le
  exact hf ⟨h0, h1⟩ ⟨hx.1, hx.2.le⟩ hxj.1

