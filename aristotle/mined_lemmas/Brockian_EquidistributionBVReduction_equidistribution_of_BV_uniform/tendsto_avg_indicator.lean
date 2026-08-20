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

lemma tendsto_avg_indicator {u : ℕ → ℝ} (hu : UniformlyDistributedMod1 u) (a b : ℝ)
    (h0 : 0 ≤ a) (hab : a ≤ b) (h1 : b ≤ 1) :
    Tendsto (avg u (Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ)))) atTop (𝓝 (b - a)) := by
  have h : avg u (Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ))) =
      fun N : ℕ =>
        (((Finset.range N).filter (fun n => Int.fract (u n) ∈ Set.Ico a b)).card : ℝ) / N :=
    funext (avg_indicator u a b)
  rw [h]
  exact hu a b h0 hab h1

