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

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Brockian.EquidistributionBVReduction

/-- The frequency with which the fractional parts of the first `N` terms of the sequence `x`
land in the interval `[a, b)`. -/

lemma tendsto_step_sum (hx : UniformlyDistributedMod1 x) {k : ℕ} (hk : 0 < k) (c : ℕ → ℝ) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.range k, c j *
        ((((Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))).card : ℝ) / N))
      atTop (𝓝 (∑ j ∈ Finset.range k, c j / k)) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  refine tendsto_finset_sum _ (fun j hj => ?_)
  have hjk : j < k := Finset.mem_range.mp hj
  have h1 : (0:ℝ) ≤ (j:ℝ)/k := by positivity
  have h2 : (j:ℝ)/k ≤ ((j:ℝ)+1)/k := by gcongr; linarith
  have h3 : ((j:ℝ)+1)/k ≤ 1 := by
    rw [div_le_one hk0]; have : j + 1 ≤ k := hjk; exact_mod_cast this
  have hlim := (hx ((j:ℝ)/k) (((j:ℝ)+1)/k) h1 h2 h3).const_mul (c j)
  have heq : c j * (((j:ℝ)+1)/k - (j:ℝ)/k) = c j / k := by field_simp; ring
  rw [heq] at hlim
  exact hlim

/-- The Birkhoff averages of a monotone function along a sequence that is uniformly distributed
mod 1 converge to its integral over `[0, 1]`. -/
