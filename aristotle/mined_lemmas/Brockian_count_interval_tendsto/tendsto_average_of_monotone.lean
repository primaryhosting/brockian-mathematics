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

open Filter Finset MeasureTheory
open scoped Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- A sequence `x : ℕ → ℝ` with values in `[0, 1)` is *uniformly distributed* if for every
`c ∈ [0, 1]` the proportion of the first `N` terms lying in `[0, c)` tends to `c`. -/

lemma tendsto_average_of_monotone (hx : UniformlyDistributed x) (hg : Monotone g) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, g (x n)) / N) atTop (𝓝 (∫ t in (0 : ℝ)..1, g t)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨k, hk⟩ := exists_nat_gt (4 * (g 1 - g 0) / δ)
  have hk0 : 0 < k := by
    by_contra hk0
    have : k = 0 := by omega
    subst this
    have h01 : 0 ≤ g 1 - g 0 := sub_nonneg.2 (hg zero_le_one)
    have : 0 ≤ 4 * (g 1 - g 0) / δ := by positivity
    simp at hk
    linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hsmall : (g 1 - g 0) / k < δ / 4 := by
    rw [div_lt_iff₀ hkR]
    rw [div_lt_iff₀ hδ] at hk
    nlinarith
  have h := abs_average_sub_integral_le hx hg hk0 (ε := δ / 4) (by linarith)
  rw [eventually_atTop] at h
  obtain ⟨N₀, hN₀⟩ := h
  refine ⟨N₀, fun N hN => ?_⟩
  have := hN₀ N hN
  rw [Real.dist_eq]
  linarith

end Monotone

/-- Clamping a real number to `[0, 1]`. -/
