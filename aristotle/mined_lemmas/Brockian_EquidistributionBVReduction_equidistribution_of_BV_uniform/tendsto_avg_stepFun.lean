import Brockian.EquidistributionBVReduction

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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set MeasureTheory
open scoped BigOperators Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- The empirical frequency with which the first `N` terms of the sequence `x`
land in the interval `[a, b)`. -/

lemma tendsto_avg_stepFun {x : ℕ → ℝ} (hx : UniformlyDistributed x) (hk : 0 < k) (c : ℕ → ℝ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, stepFun k c (x n)) / N) atTop
      (𝓝 (∑ i ∈ Finset.range k, c i / k)) := by
  classical
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have key : ∀ N : ℕ, (∑ n ∈ Finset.range N, stepFun k c (x n)) / N
      = ∑ i ∈ Finset.range k, c i * freq x ((i : ℝ) / k) (((i : ℝ) + 1) / k) N := by
    intro N
    rw [sum_stepFun, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [freq, mul_div_assoc]
  simp only [key]
  refine tendsto_finset_sum _ fun i hi => ?_
  have hi' : i < k := Finset.mem_range.1 hi
  have h1 : (0 : ℝ) ≤ (i : ℝ) / k := by positivity
  have h2 : (i : ℝ) / k ≤ ((i : ℝ) + 1) / k := by
    gcongr
    linarith
  have h3 : ((i : ℝ) + 1) / k ≤ 1 := by
    rw [div_le_one hk']
    have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi'
    linarith
  have h := (hx.2 ((i : ℝ) / k) (((i : ℝ) + 1) / k) h1 h2 h3).const_mul (c i)
  have heq : ((i : ℝ) + 1) / k - (i : ℝ) / k = 1 / k := by
    rw [div_sub_div_same]; norm_num
  rw [heq] at h
  simpa [mul_one_div] using h

end Aux

/-- Lower and upper Riemann sums for a monotone function bracket its integral. -/
