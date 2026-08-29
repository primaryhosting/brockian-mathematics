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

open scoped BigOperators
open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace Brockian.EquidistributionBVReduction

/-- The (right-continuous) step function jumping from `0` to `1` at `c`. -/

theorem integral_stepFun {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    (∫ t in (0 : ℝ)..1, stepFun c t) = 1 - c := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  have hset : (fun t => stepFun c t) = Set.indicator (Set.Ici c) (fun _ => (1 : ℝ)) := by
    funext t; simp [stepFun, Set.indicator_apply]
  rw [hset, MeasureTheory.setIntegral_indicator measurableSet_Ici,
    MeasureTheory.setIntegral_const]
  have hvol : volume (Set.Ioc (0 : ℝ) 1 ∩ Set.Ici c) = ENNReal.ofReal (1 - c) := by
    apply le_antisymm
    · calc volume (Set.Ioc (0 : ℝ) 1 ∩ Set.Ici c) ≤ volume (Set.Icc c 1) := by
            apply measure_mono
            rintro t ⟨⟨_, h2⟩, h3⟩
            exact ⟨h3, h2⟩
        _ = ENNReal.ofReal (1 - c) := by rw [Real.volume_Icc]
    · calc ENNReal.ofReal (1 - c) = volume (Set.Ioo c 1) := by rw [Real.volume_Ioo]
        _ ≤ volume (Set.Ioc (0 : ℝ) 1 ∩ Set.Ici c) := by
            apply measure_mono
            rintro t ⟨h1, h2⟩
            exact ⟨⟨lt_of_le_of_lt hc h1, h2.le⟩, h1.le⟩
  rw [measureReal_def, hvol, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - c), smul_eq_mul,
    mul_one]

