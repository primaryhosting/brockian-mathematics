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

open Filter Topology

namespace Brockian.EquidistributionBVReduction

/-- The number of "configurations" below `N` in the arithmetic progression
`a mod q`, i.e. the cardinality of `{n < N | n ≡ a [MOD q]}`. -/

theorem configCount_over_main_tendsto (q a : ℕ) (hq : 0 < q) :
    Tendsto (fun N : ℕ => (configCount q a N : ℝ) / mainTerm q N) atTop (𝓝 1) := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  -- the error term `q / N` tends to `0`
  have herr : Tendsto (fun N : ℕ => (q : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      ((tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul (q : ℝ))
  rw [Metric.tendsto_atTop] at herr ⊢
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := herr ε hε
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right N₀ 1) hN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hb := abs_mul_configCount_sub_le q a N hq
  have key : (configCount q a N : ℝ) / mainTerm q N - 1
      = ((q : ℝ) * (configCount q a N : ℝ) - (N : ℝ)) / (N : ℝ) := by
    rw [mainTerm, div_div_eq_mul_div]
    field_simp
  have hdist : dist ((configCount q a N : ℝ) / mainTerm q N) 1 ≤ (q : ℝ) / (N : ℝ) := by
    rw [Real.dist_eq, key, abs_div, abs_of_pos hNR]
    gcongr
  have h2 := hN₀ N (le_trans (le_max_left N₀ 1) hN)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
  linarith

end Brockian.EquidistributionBVReduction

