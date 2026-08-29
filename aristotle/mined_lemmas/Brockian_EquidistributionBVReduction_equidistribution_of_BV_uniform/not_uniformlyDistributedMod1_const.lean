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

lemma not_uniformlyDistributedMod1_const : ¬ UniformlyDistributedMod1 (fun _ : ℕ => (0:ℝ)) := by
  intro h
  have h2 := h (1/2) 1 (by norm_num) (by norm_num) le_rfl
  have hzero : freq (fun _ : ℕ => (0:ℝ)) (1/2) 1 = fun _ => 0 := by
    funext N
    simp [freq, Int.fract]
  rw [hzero] at h2
  have := tendsto_nhds_unique h2 tendsto_const_nhds
  norm_num at this

section Monotone

variable {x : ℕ → ℝ} {g : ℝ → ℝ}

/-- The fibers of `n ↦ ⌊k * frac (x n)⌋₊` are exactly the sets of indices whose fractional part
lies in the corresponding subinterval of the uniform partition of `[0, 1)` into `k` pieces. -/
