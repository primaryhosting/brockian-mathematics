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

lemma tendsto_riemann_sums (hx : EquidistributedMod1 x) {K : ℕ} (hK : 0 < K) (c : ℕ → ℝ) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.range K,
        ((configCount x (Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K)) N : ℝ) / N) * c j)
      atTop (𝓝 (∑ j ∈ Finset.range K, (1 / (K:ℝ)) * c j)) := by
  have hK' : (0:ℝ) < K := by exact_mod_cast hK
  refine tendsto_finset_sum _ ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  have hb : ((j:ℝ) + 1) / K ≤ 1 := by
    rw [div_le_one hK']
    have : (j:ℝ) + 1 ≤ K := by exact_mod_cast hj
    linarith
  have hab : (j:ℝ)/K ≤ ((j:ℝ)+1)/K := by
    rw [div_le_div_iff_of_pos_right hK']; linarith
  have h := hx ((j:ℝ)/K) (((j:ℝ)+1)/K) (by positivity) hab hb
  have hlen : ((j:ℝ)+1)/K - (j:ℝ)/K = 1 / K := by field_simp; ring
  rw [hlen] at h
  exact h.mul_const (c j)

/-- Cesàro averages of a function that is monotone on `[0,1]` along an equidistributed
sequence converge to its integral. -/
