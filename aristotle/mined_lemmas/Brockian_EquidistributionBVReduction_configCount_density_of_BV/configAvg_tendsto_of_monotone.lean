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
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.EquidistributionBVReduction

open Filter Set MeasureTheory

/-- `configCount x S N` is the number of indices `n < N` whose fractional part
`Int.fract (x n)` lands in the "configuration window" `S`. -/

theorem configAvg_tendsto_of_monotone (hx : EquidistributedMod1 x) (G : ℝ → ℝ)
    (hG : Monotone G) :
    Tendsto (configAvg x G) atTop (nhds (∫ t in (0 : ℝ)..1, G t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, 0 < k ∧ (G 1 - G 0) / k < ε / 2 := by
    obtain ⟨k, hk⟩ := exists_nat_gt (max 1 ((G 1 - G 0) * 2 / ε))
    have hk1 : (1 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
    have hkpos : (0 : ℝ) < k := by linarith
    refine ⟨k, by exact_mod_cast hkpos, ?_⟩
    rw [div_lt_iff₀ hkpos]
    have h' : (G 1 - G 0) * 2 / ε < k := lt_of_le_of_lt (le_max_right _ _) hk
    rw [div_lt_iff₀ hε] at h'
    linarith
  have hlow := tendsto_lowerSum x hx G k hk1
  have hup := tendsto_upperSum x hx G k hk1
  rw [Metric.tendsto_atTop] at hlow hup
  obtain ⟨N1, hN1⟩ := hlow (ε / 4) (by linarith)
  obtain ⟨N2, hN2⟩ := hup (ε / 4) (by linarith)
  refine ⟨max 1 (max N1 N2), fun N hN => ?_⟩
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hN)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have h1 := hN1 N (le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hN)
  have h2 := hN2 N (le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hN)
  rw [Real.dist_eq, abs_lt] at h1 h2
  have hlowle : (∑ i ∈ Finset.range k,
      G ((i : ℝ) / k) *
        (configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ)) / N ≤
      configAvg x G N := by
    rw [configAvg]
    gcongr
    exact lower_le_sum x G hG k N hk1
  have hupge : configAvg x G N ≤ (∑ i ∈ Finset.range k,
      G (((i : ℝ) + 1) / k) *
        (configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ)) / N := by
    rw [configAvg]
    gcongr
    exact sum_le_upper x G hG k N hk1
  have hLI := lowerSum_le_integral G hG k hk1
  have hIU := integral_le_upperSum G hG k hk1
  have hUL := upperSum_sub_lowerSum G k hk1
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end MonotoneCase

/-- **Config-count density from bounded variation.**  If `x` is equidistributed modulo
one and `f` has bounded variation on `[0,1]`, then the Cesàro averages of `f` along the
fractional parts of `x` converge to the integral of `f` over `[0,1]`. -/
