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

lemma tendsto_avg_stepFn {u : ℕ → ℝ} (hu : UniformlyDistributedMod1 u) {m : ℕ} (hm : 0 < m)
    (c : ℕ → ℝ) :
    Tendsto (avg u (stepFn m c)) atTop (𝓝 ((∑ i ∈ Finset.range m, c i) / m)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h : avg u (stepFn m c) = fun N : ℕ =>
      ∑ i ∈ Finset.range m, c i *
        avg u (Set.indicator (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) (fun _ => (1 : ℝ))) N :=
    funext (avg_stepFn u m c)
  rw [h]
  have hlim : Tendsto (fun N : ℕ =>
      ∑ i ∈ Finset.range m, c i *
        avg u (Set.indicator (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) (fun _ => (1 : ℝ))) N)
      atTop (𝓝 (∑ i ∈ Finset.range m, c i * (1 / m))) := by
    apply tendsto_finset_sum
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have h0 : (0 : ℝ) ≤ (i : ℝ) / m := by positivity
    have hab : (i : ℝ) / m ≤ ((i : ℝ) + 1) / m := by gcongr; linarith
    have h1 : ((i : ℝ) + 1) / m ≤ 1 := by
      rw [div_le_one hm']
      have : (i : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hi'
      linarith
    have hlen : ((i : ℝ) + 1) / m - (i : ℝ) / m = 1 / m := by field_simp; ring
    have := tendsto_avg_indicator hu ((i : ℝ) / m) (((i : ℝ) + 1) / m) h0 hab h1
    rw [hlen] at this
    exact tendsto_const_nhds.mul this
  simpa [Finset.sum_div, mul_one_div] using hlim

