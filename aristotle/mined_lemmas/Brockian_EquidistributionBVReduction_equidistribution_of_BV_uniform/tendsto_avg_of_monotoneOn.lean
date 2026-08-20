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

theorem tendsto_avg_of_monotoneOn {u : ℕ → ℝ} (hu : UniformlyDistributedMod1 u) {f : ℝ → ℝ}
    (hf : MonotoneOn f (Set.Icc 0 1)) :
    Tendsto (avg u f) atTop (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  set I : ℝ := ∫ x in (0 : ℝ)..1, f x with hI
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose a fine enough partition
  obtain ⟨m0, hm0⟩ := exists_nat_gt ((f 1 - f 0) * 3 / ε)
  set m : ℕ := m0 + 1 with hmdef
  have hm : 0 < m := Nat.succ_pos _
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmgt : (f 1 - f 0) * 3 / ε < m := by
    refine lt_of_lt_of_le hm0 ?_
    exact_mod_cast Nat.le_succ m0
  have hfine : (f 1 - f 0) / m < ε / 3 := by
    have h1 : (f 1 - f 0) * 3 < m * ε := (div_lt_iff₀ hε).mp hmgt
    rw [div_lt_div_iff₀ hm' (by norm_num : (0 : ℝ) < 3)]
    linarith
  set Sl : ℝ := (∑ i ∈ Finset.range m, f ((i : ℝ) / m)) / m with hSl
  set Su : ℝ := (∑ i ∈ Finset.range m, f (((i : ℝ) + 1) / m)) / m with hSu
  have hlow : Sl ≤ I := lower_sum_le_integral hf hm
  have hupp : I ≤ Su := integral_le_upper_sum hf hm
  have hdiff : Su - Sl = (f 1 - f 0) / m := by
    have h := upper_sub_lower_sum (f := f) (m := m)
    have hmm : ((m : ℝ)) / m = 1 := by field_simp
    have hzz : ((0 : ℝ)) / m = 0 := by simp
    rw [hmm, hzz] at h
    exact h
  -- the two step functions
  have hLtend : Tendsto (avg u (stepFn m (fun i => f ((i : ℝ) / m)))) atTop (𝓝 Sl) :=
    tendsto_avg_stepFn hu hm _
  have hUtend : Tendsto (avg u (stepFn m (fun i => f (((i : ℝ) + 1) / m)))) atTop (𝓝 Su) :=
    tendsto_avg_stepFn hu hm _
  rw [Metric.tendsto_atTop] at hLtend hUtend
  obtain ⟨N1, hN1⟩ := hLtend (ε / 3) (by linarith)
  obtain ⟨N2, hN2⟩ := hUtend (ε / 3) (by linarith)
  refine ⟨max N1 N2, fun N hN => ?_⟩
  have hb1 := hN1 N (le_trans (le_max_left _ _) hN)
  have hb2 := hN2 N (le_trans (le_max_right _ _) hN)
  rw [Real.dist_eq, abs_lt] at hb1 hb2 ⊢
  have hle1 : avg u (stepFn m (fun i => f ((i : ℝ) / m))) N ≤ avg u f N :=
    avg_mono u (fun x hx => stepFn_lower_le hf hm hx) N
  have hle2 : avg u f N ≤ avg u (stepFn m (fun i => f (((i : ℝ) + 1) / m))) N :=
    avg_mono u (fun x hx => le_stepFn_upper hf hm hx) N
  constructor <;> [linarith [hb1.1, hb2.2]; linarith [hb1.1, hb2.2]]

/-- **Equidistribution against functions of bounded variation.**
If `u` is uniformly distributed mod one and `f` has bounded variation on `[0,1]`, then the
Cesàro averages of `f` along the fractional parts of `u` converge to `∫₀¹ f`. -/
