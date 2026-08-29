import Mathlib
import RequestProject.Brockian.EquidistributionBVReduction

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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset Set
open scoped Topology BigOperators Classical

set_option maxHeartbeats 1000000

namespace Brockian
namespace EquidistributionBVReduction

/-- `countIn x a b N` is the number of indices `n < N` with `x n ∈ [a, b)`. -/

lemma tendsto_weighted_count (hud : UniformlyDistributed x) (hk : 0 < k) (c : ℕ → ℝ) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.range k,
        c j * ((countIn x ((j : ℝ) / k) (((j : ℝ) + 1) / k) N : ℝ) / (N : ℝ))) atTop
      (𝓝 (∑ j ∈ Finset.range k, c j * (1 / (k : ℝ)))) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine tendsto_finset_sum _ ?_
  intro j hj
  have hj' : (j : ℝ) + 1 ≤ k := by exact_mod_cast Finset.mem_range.1 hj
  have h1 : (0 : ℝ) ≤ (j : ℝ) / k := by positivity
  have h2 : (j : ℝ) / k ≤ ((j : ℝ) + 1) / k := by
    gcongr
    linarith
  have h3 : ((j : ℝ) + 1) / k ≤ 1 := by rw [div_le_one hk']; exact hj'
  have hlim := (hud ((j : ℝ) / k) (((j : ℝ) + 1) / k) h1 h2 h3).const_mul (c j)
  have heq : ((j : ℝ) + 1) / k - (j : ℝ) / k = 1 / (k : ℝ) := by field_simp; ring
  rw [heq] at hlim
  exact hlim

/-- The integral is bounded above by the upper Darboux sum. -/
